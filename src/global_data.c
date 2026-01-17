/**
 * @file global_data.c
 * @brief Global functions and data used in SR proof labeling, trimming, and checking.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-10
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>

#include "xmalloc.h"
#include "global_data.h"
#include "lit_occ.h"
#include "logger.h"

/** Determines if the sign bit is set to mark a deleted clause. */
#define IS_DELETED_CLAUSE(x)      ((x) & SRID_MSB)

/** Removes the sign bit from the clause index value to remove deletion info. */
#define CLAUSE_IDX(x)             ((x) & (~SRID_MSB))

/** Sets the sign bit for the clause index value to logically delete it. */
#define DELETE_CLAUSE(x)          ((x) | SRID_MSB)

// TODO: Instead of floating point, use numerator and denominator.
#define DELETION_GC_NUMER           1
#define DELETION_GC_DENOM           4

////////////////////////////////////////////////////////////////////////////////

parsing_strategy_t p_strategy = PS_EAGER;

int *lits_db = NULL;
srid_t lits_db_size = 0;
srid_t lits_db_alloc_size = 0;

/** The total number of literals that have been "deleted" from the literal database.
 *  Cleared during `delete_clause` when the deletion percentage clears a certain threshold.
 * 
 *  As the checker/trimmer consumes the SR proof/certificate, it will delete clauses.
 *  The deletions are marked by setting the most-significant bit of the entries
 *  in `formula`, so the memory in `lits_db` is not actually freed (as it might 
 *  if lits_db were instead a 2D array, rather than a flat 1D array). As a result,
 *  the sizes of the deleted clauses are accumulated here. When a threshold is
 *  reached, the literals in `lits_db` are shifted down to overwrite the "deleted"
 *  literals. The indexes in `formula` are updated to reflect the new positions.
 */
static srid_t lits_db_deleted_size = 0;

srid_t *formula = NULL;
srid_t formula_size = 0;
srid_t formula_alloc_size = 0;

srid_t num_cnf_clauses;
int num_cnf_vars;

ullong *alpha = NULL;
ullong *subst_generations = NULL;
int *subst_mappings = NULL;
int alpha_subst_alloc_size = 0;
ullong alpha_generation = 0;
ullong subst_generation = 0;

range_array_t witnesses;

uint new_clause_size = 0;
int max_var = -1;
int derived_empty_clause = 0;

////////////////////////////////////////////////////////////////////////////////

int intcmp(const void *a, const void *b) {
  return (*(int*)a - *(int*)b); 
}

int absintcmp(const void *a, const void *b) {
  int ia = *(int*)a;
  int ib = *(int*)b;
  return (abs(ia) - abs(ib)); 
}

int llongcmp(const void *a, const void *b) {
  return (*(llong*)a - *(llong*)b); 
}

int absllongcmp(const void *a, const void *b) {
  llong ia = *(llong*)a;
  llong ib = *(llong*)b;
  return (llabs(ia) - llabs(ib)); 
}

// TODO: determine how to mark functions as inline wrt header files. Profile later?

void init_global_data(void) {
  lits_db_alloc_size = num_cnf_clauses * 4;
  formula_alloc_size = num_cnf_clauses * 2;
  alpha_subst_alloc_size = num_cnf_vars * 4;
  max_var = num_cnf_vars - 1;

  lits_db_size = 0;
  formula_size = 0;

  lits_db = xmalloc(lits_db_alloc_size * sizeof(int));
  formula = xmalloc(formula_alloc_size * sizeof(srid_t));
  formula[0] = 0;

  alpha = xcalloc(alpha_subst_alloc_size, sizeof(ullong));
  subst_generations = xcalloc(alpha_subst_alloc_size, sizeof(ullong));
  subst_mappings = xmalloc(alpha_subst_alloc_size * sizeof(int));

  switch (p_strategy) {
    case PS_EAGER:
      // When eagerly parsing, we want a good amount of pre-allocated memory
      ra_init(&witnesses, num_cnf_clauses * 5, formula_alloc_size, sizeof(int));
      break;
    case PS_STREAMING:
      // When streaming, we only expect a single witness at a time, which is
      // roughly bounded above by twice the number of variables
      ra_init(&witnesses, num_cnf_vars * 2, 2, sizeof(int));
      break;
    default: log_fatal_err("Unknown parsing strategy: %d.", p_strategy);
  }
}

/**
 * @brief Prints the result of proof checking.
 * 
 * If the empty clause was derived and `derived_empty_clause` was set,
 * then the proof has been `VERIFIED UNSAT`. Otherwise, (assuming forwards
 * proof checking), the proof is `VALID`.
 * 
 * The result is printed regardless of the verbosity level, but other
 * comments explaining the result can be suppressed with the `-q` flag.
 */
void print_proof_checking_result(void) {
  if (derived_empty_clause) {
    log_raw(VL_QUIET, "s VERIFIED UNSAT\n");
  } else {
    log_raw(VL_QUIET, "s VALID\n");
    logc("A valid proof, without an empty clause.");
  }
}

// Assumes that VAR_FROM_LIT(lit) < alpha_subst_size
inline void set_lit_for_alpha(int lit, ullong gen) {
  int var = VAR_FROM_LIT(lit);
  // This flips the least-significant bit if `lit` is negated
  alpha[var] = gen ^ IS_NEG_LIT(lit);
}

// Compares against alpha_generation
inline peval_t peval_lit_under_alpha(int lit) {
  ullong gen = alpha[VAR_FROM_LIT(lit)];
  if (gen >= alpha_generation) {
    return IS_NEG_GEN(gen) ^ IS_NEG_LIT(lit);
  } else {
    return UNASSIGNED;
  }
}

// Returns the number of unassigned literals if not satisfied, -1 if satisfied.
int peval_clause_under_alpha(srid_t clause_index) {
  FATAL_ERR_IF(is_clause_deleted(clause_index),
    "Trying to evaluate a deleted clause %lld.",
    TO_DIMACS_CLAUSE(clause_index));

  int *clause_iter = get_clause_start_unsafe(clause_index);
  int *clause_end = get_clause_end(clause_index);
  int num_unassigned = 0;
  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    peval_t peval_lit = peval_lit_under_alpha(lit);
    switch (peval_lit) {
      case TT: return -1;
      case UNASSIGNED: num_unassigned++; break;
      case FF: break;
      default: log_fatal_err("Corrupted peval for lit %d and clause %lld.",
          TO_DIMACS_LIT(lit), TO_DIMACS_CLAUSE(clause_index));
    }
  }

  return num_unassigned;
}

static void set_mapping_for_subst(int lit, int lit_mapping) {
  FATAL_ERR_IF(lit < 0 || lit_mapping < SUBST_FF,
    "set_mapping_for_subst(): tried to map %d to %d", lit, lit_mapping);
  int var = VAR_FROM_LIT(lit);
  subst_generations[var] = subst_generation;
  // Negates the mapping if the original `lit` is negated
  subst_mappings[var] = lit_mapping ^ IS_NEG_LIT(lit);
}

// Returns the lit value of subst(lit). Can return SUBST_TT/_FF.
// Compares against subst_generation.
int map_lit_under_subst(int lit) {
  int var = VAR_FROM_LIT(lit);
  ullong gen = subst_generations[var];
  if (gen >= subst_generation) {
    // This negates the mapping if `lit` is negated
    return subst_mappings[var] ^ IS_NEG_LIT(lit);
  } else {
    return lit;
  }
}

/**
 * @brief Inserts a literal into the literal database, adjusts `max_var`,
 *        and increments the `new_clause_size`.
 * 
 * In addition, this function updates `max_var` and allocates data structures
 * that depend on `max_var` for their allocation size, if necessary.
 * 
 * Does not perform first-last updates. For that, call either
 * `commit_clause_with_first_last_update()` or
 * `perform_clause_first_last_update()`.
 * 
 * @param lit The 0-indexed, non-DIMACS literal to insert.
 */
void insert_lit(int lit) {
  // Insert the literal into the literal database
  INSERT_ARR_ELT_CONCAT(lits_db, sizeof(int), lit);
  new_clause_size++;

  // Resize the other var-indexed arrays if new max would exceed allocated size
  int var = VAR_FROM_LIT(lit);
  max_var = MAX(max_var, var);
  if (max_var >= alpha_subst_alloc_size) {
    int old_size = alpha_subst_alloc_size;

    alpha_subst_alloc_size = RESIZE(max_var);
    alpha = xrecalloc(alpha, old_size * sizeof(ullong),
      alpha_subst_alloc_size * sizeof(ullong));
    subst_generations = xrecalloc(subst_generations, old_size * sizeof(ullong),
      alpha_subst_alloc_size * sizeof(ullong));
    subst_mappings = xrealloc(subst_mappings,
      alpha_subst_alloc_size * sizeof(int));
  }
}

/** @brief Commits the current set of uncommitted literals to a new 
 * formula clause.
 * 
 * This function officially adds the set of uncommitted literals that
 * were added via `insert_lit()` or `insert_lit_no_first_last_update()`
 * to the formula by increasing the `formula_size` by 1 and adding an index
 * "pointer" to the next set of uncommitted literals.
 * 
 * The function resizes the `formula` array containing the clause index
 * pointers if the array is too small.
 */
void commit_clause(void) {
  // We increment formula_size first to ensure that one past the last entry is allocated
  // We use this to store the clause_index for the incoming clause
  formula_size++;  // Cap off the current clause and prepare the next one
  RESIZE_ARR(formula, formula_alloc_size, formula_size, sizeof(srid_t));
  formula[formula_size] = lits_db_size;
}

void commit_and_delete_clause(void) {
  commit_clause();
  delete_clause(formula_size - 1);
}

int is_clause_deleted(srid_t clause_index) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "is_clause_deleted(): Clause index %lld was out of bounds (%lld).",
    clause_index, formula_size);
  return IS_DELETED_CLAUSE(formula[clause_index]);
}

static inline void gc_lits_db(void) {
  // Don't garbage collect unless we've deleted enough literals
  if (lits_db_deleted_size * DELETION_GC_DENOM
        <= lits_db_size * DELETION_GC_NUMER) return;

  srid_t insert_index = 0;
  srid_t clause_idx;
  srid_t next_clause_idx = formula[0]; // First loop takes value of next_clause_ptr
  for (srid_t i = 0; i < formula_size; i++) {
    clause_idx = next_clause_idx;
    next_clause_idx = formula[i + 1]; // Lemma: allowed, b/c one past is allocated

    if (IS_DELETED_CLAUSE(clause_idx)) {
      // Put the deleted clause's pointer at the insert index, but keep it deleted
      // That way, the previous clause still knows its size
      formula[i] = DELETE_CLAUSE(insert_index);
    } else {
      if (insert_index == clause_idx) {
        insert_index = CLAUSE_IDX(next_clause_idx); // No moving, bump up insert index
      } else {
        // Move the literals down and update formula clause pointer
        formula[i] = insert_index;
        srid_t size = CLAUSE_IDX(next_clause_idx) - clause_idx;
        memmove(lits_db + insert_index, lits_db + clause_idx, size * sizeof(int));
        insert_index += size;
      }
    }
  }

  // Finally, update the place to put a new clause, moving "pending" literals if any
  // Lemma: the final clause is not deleted
  clause_idx = next_clause_idx;
  formula[formula_size] = insert_index;
  srid_t size = lits_db_size - clause_idx;
  memmove(lits_db + insert_index, lits_db + clause_idx, size * sizeof(int));
  lits_db_size = insert_index + size;
  lits_db_deleted_size = 0;
}

void soft_delete_clause(srid_t clause_index) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "soft_delete_clause(): Clause index %lld was out of bounds (%lld).",
    clause_index, formula_size);

  srid_t clause_ptr = formula[clause_index];

  FATAL_ERR_IF(IS_DELETED_CLAUSE(clause_ptr),
    "Clause %lld was already deleted.", TO_DIMACS_CLAUSE(clause_index)); 

  formula[clause_index] = DELETE_CLAUSE(clause_ptr);
}

void soft_undelete_clause(srid_t clause_index) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "soft_undelete_clause(): Clause index %lld was out of bounds (%lld).",
    clause_index, formula_size);

  srid_t clause_ptr = formula[clause_index];

  FATAL_ERR_IF(!IS_DELETED_CLAUSE(clause_ptr),
    "soft_undelete_clause(): Clause %lld was not deleted.",
    TO_DIMACS_CLAUSE(clause_index)); 

  formula[clause_index] = CLAUSE_IDX(clause_ptr); 
}

void delete_clause(srid_t clause_index) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "delete_clause(): Clause index %lld was out of bounds (%lld).",
    clause_index, formula_size);
  
  srid_t clause_ptr = formula[clause_index];
  
  FATAL_ERR_IF(IS_DELETED_CLAUSE(clause_ptr),
    "Clause %lld was already deleted.", TO_DIMACS_CLAUSE(clause_index));

  srid_t next_clause_ptr = CLAUSE_IDX(formula[clause_index + 1]);

  // TODO: Could break if delete clause just added(?)
  lits_db_deleted_size += next_clause_ptr - clause_ptr;
  formula[clause_index] = DELETE_CLAUSE(clause_ptr);
  gc_lits_db(); // If we deleted enough from `lits_db`, garbage collect
}

inline int *get_clause_start_unsafe(srid_t clause_index) {
  return lits_db + formula[clause_index];
}

int *get_clause_start(srid_t clause_index) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "get_clause_start(): Clause %lld was out of bounds (%lld).",
    TO_DIMACS_CLAUSE(clause_index), formula_size);
  return lits_db + CLAUSE_IDX(formula[clause_index]);
}

int *get_clause_end_unsafe(srid_t clause_index) {
  if (clause_index == formula_size) {
    return lits_db + lits_db_size;
  } else {
    return lits_db + formula[clause_index + 1];
  }
}

int *get_clause_end(srid_t clause_index) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "get_clause_end(): Clause %lld was out of bounds (%lld).",
    TO_DIMACS_CLAUSE(clause_index), formula_size);

  if (clause_index == formula_size) {
    return lits_db + lits_db_size;
  } else {
    return lits_db + CLAUSE_IDX(formula[clause_index + 1]);
  }
}

// TODO: What should this return for the new clause, if not yet added?
uint get_clause_size(srid_t clause_index) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "get_clause_size(): Clause index %lld was out of bounds (%lld).",
    clause_index, formula_size);

  if (clause_index == formula_size) {
    return (uint) (lits_db_size - CLAUSE_IDX(formula[clause_index]));
  } else {
    return (uint) (CLAUSE_IDX(formula[clause_index + 1])
      - CLAUSE_IDX(formula[clause_index]));
  }
}

/**
 * @brief Sorts the literals in the uncommitted, newly-parsed clause,
 *        removes duplicates, and checks for tautologies.
 * 
 * This function sorts the literals of the new clause in increasing order
 * of magnitude, removes duplicate literals, and detects if the clause
 * is a tautology. The `new_clause_size` is updated to reflect the number
 * of distinct literals.
 * 
 * Assumes the caller has set `new_clause_size` to the correct number
 * of uncommitted literals. If the caller uses `insert_lit()`, then
 * this handled automatically, as long as `new_clause_size` was set to
 * `0` before parsing a new clause.
 * 
 * If `1` is returned, then the clause may not be deduplicated, but
 * all distinct literals will still be present and sorted. The value of
 * `new_clause_size` will be unaffected.
 * 
 * @param is_sr `1` if the first literal (i.e., the pivot) should be
 *              fixed in the 0th position, regardless of its value.
 * @return `1` if the clause is a tautology, and `0` otherwise.
 */
static int sort_and_dedup_new_clause(int is_sr) {
  // Units and the empty clause are already sorted and cannot be tautologies
  // Also, `qsort()` has undefined behavior on 0 or 1 elements
  // (Or rather, I ran into some trouble at very low sizes in `dsr-trim`)
  if (new_clause_size <= 1) {
    return 0;
  }

  /* 
   * We now sort the literals of the clause in increasing order of magnitude,
   * which standardizes the representation of the clause. Sorting the literals
   * in this fashion also lets us efficiently detect duplicated literals
   * and whether the clause is a tautology.
   * 
   * In almost all cases, clauses will not be tautologies and won't
   * contain duplicated literals, but we do this check to be safe.
   * Certainly when it comes to efficient RAT proof checking, we want
   * to have an accurate count of how many times each literal occurs.
   * See `lsr-check.c` for more information.
   * 
   * As for why we especially want to check for tautologies:
   * When it comes to proof checking, tautological clauses are useless, and
   * so the caller might want to ignore tautologies, or reject CNF formulas
   * that contain tautologies.
   * 
   * The way we remove duplicate literals is somewhat complicated.
   * After sorting, we move a read pointer over the clause. Any time we
   * find a duplicate literal, we skip it, and we write subsequent literals
   * to a `write_ptr` that lags behind the read pointer. This is an in-place
   * version of looping over one array and writing valid elements to a
   * second array, ignoring invalid elements.
   */

  int *read_ptr = get_clause_start(formula_size) + is_sr;
  int *write_ptr = read_ptr + 1; // First literal is always in the correct spot
  int negated_pivot = (is_sr) ? NEGATE_LIT(read_ptr[-1]) : -1;

  // Edge case: binary SR clauses. Check if the second literal causes tautology
  if (is_sr && new_clause_size == 2) {
    return (read_ptr[0] == negated_pivot);
  }

  qsort(read_ptr, new_clause_size - is_sr, sizeof(int), absintcmp);

  // If we are sorting an SR clause, we need to keep the pivot in mind.
  // The SR parser should never place two copies of the pivot in the clause,
  // but we could have a tautology on the pivot.

  int skipped_lits = 0;
  int prev_lit;
  int lit = read_ptr[0];

  // Since the loop below does all adjacent comparisons, we add a special
  // check for the very first literal after the pivot
  if (is_sr && lit == negated_pivot) {
    return 1;
  }

  // Loop over the literals and compare adjacent literals
  // If the literals are the same, don't increment the write pointer
  // If the literals are negations, then we have a tautology
  uint comparisons_to_make = new_clause_size - (1 + is_sr);
  for (uint i = 0; i < comparisons_to_make; i++) {
    prev_lit = lit;
    read_ptr++;
    lit = *read_ptr;

    if (prev_lit == lit) {
      skipped_lits++;
    } else if (prev_lit == NEGATE_LIT(lit) || (is_sr && lit == negated_pivot)) {
      return 1;
    } else {
      // Only write a literal if the write pointer has lagged behind
      // Otherwise, writing `lit` is a no-op, as it would write in-place
      if (skipped_lits > 0) {
        *write_ptr = lit;
      }

      write_ptr++;
    }
  }

  new_clause_size -= skipped_lits;
  lits_db_size -= skipped_lits;
  return 0;
}

// Sorts and deduplicates a new uncommitted CNF clause.
// See `sort_and_dedup_new_clause()` in `global_data.c`.
inline int sort_and_dedup_new_cnf_clause(void) {
  return sort_and_dedup_new_clause(0);
}

// Sorts and deduplicates a new uncommitted SR clause.
// See `sort_and_dedup_new_clause()` in `global_data.c`.
inline int sort_and_dedup_new_sr_clause(void) {
  return sort_and_dedup_new_clause(1);
}


/**
 * @brief Scrubs the existence of any clause after `clause_index`, instead
 *        making the clause after be the empty clause.
 * 
 * An `EAGER` parsing strategy might parse more clauses than are needed to
 * derive the empty clause, so to maintain data structure invariants
 * regarding `formula_size` etc., this function discards any clauses above
 * `clause_index`, and then caps the formula with the empty clause.
 * 
 * @param clause_index The highest clause index to keep in the formula.
 */
void discard_formula_after_clause(srid_t clause_index) {
  FATAL_ERR_IF(clause_index >= formula_size,
    "Cannot discard the formula after clause %lld, as it is out of bounds.",
    TO_DIMACS_CLAUSE(clause_index));

  lits_db_size = formula[clause_index + 1];
  formula_size = clause_index + 2;
  formula[clause_index + 2] = lits_db_size;
}

inline int *get_witness_start(srid_t line_num) {
  if (p_strategy == PS_EAGER) {
    return ((int *) ra_get_range_start(&witnesses, line_num));
  } else {
    return ((int *) ra_get_range_start(&witnesses, 0));
  }
}

inline int *get_witness_end(srid_t line_num) {
  if (p_strategy == PS_EAGER) {
    return ((int *) ra_get_range_start(&witnesses, line_num + 1));
  } else {
    return ((int *) ra_get_range_start(&witnesses, 1));
  }
}

inline int get_witness_size(srid_t line_num) {
  return (int) (get_witness_end(line_num) - get_witness_start(line_num));
}

// Expands the min/max clause range `fl` to include the range for `lit`.
static void add_fl_for_lit(int lit, lit_occ_t *lc, fl_clause_t *fl) {
  fl_clause_t *lit_fl = get_first_last_clause_for_lit(lc, lit);
  if (lit_fl->first_clause != -1) {
    fl->first_clause = MIN(fl->first_clause, lit_fl->first_clause); 
    fl->last_clause = MAX(fl->last_clause, lit_fl->last_clause);
  }
}

/**
 * @brief Moves the substitution mappings into `subst`.
 * 
 * @param line_id The 0-indexed line ID of the substitution witness.
 *  If the parsing strategy is `PS_EAGER`, this ID corresponds to the
 *  range array index in `witnesses`. Otherwise, the line ID is ignored.
 
 */
void assume_subst(srid_t line_num) {
  int *witness_iter = get_witness_start(line_num);
  int *witness_end = get_witness_end(line_num);

  int seen_pivot_divider = 0;
  int pivot = witness_iter[0];
  int pivot_var = VAR_FROM_LIT(pivot);

  set_mapping_for_subst(pivot, SUBST_TT);
  witness_iter++; // Move the iterator past the pivot

  // For all other literals l in the witness:
  // 1. Check that VAR(l) hasn't been set in `subst` yet
  // 2. Set its mapping
  for (; witness_iter < witness_end; witness_iter++) {
    int lit = *witness_iter;
    if (lit == WITNESS_TERM) break;
    int var = VAR_FROM_LIT(lit);

    // Error if we have already set a variable in the substitution.
    // This ensures no variable appears twice.
    // Note that the pivot can be re-set in the substitution portion
    FATAL_ERR_IF(subst_generations[var] == subst_generation && var != pivot_var,
      "[line %lld] Literal %d in witness was already set.",
      LINE_ID_FROM_LINE_NUM(line_num), TO_DIMACS_LIT(lit));

    if (!seen_pivot_divider) {
      if (lit == pivot) {
        seen_pivot_divider = 1; // Skip the pivot divider
      } else {
        set_mapping_for_subst(lit, SUBST_TT);
      }
    } else {
      witness_iter++;
      int mapped_lit = *witness_iter;
      set_mapping_for_subst(lit, mapped_lit);
    }
  }
}

/**
 * @brief Store the first/last range of clauses for the substitution in `fl`.
 * 
 * To minimize the number of reduced clauses to check during SR checking,
 * we compute the range of clauses reduced by the substitution.
 * For each literal perturbed by the witness, we add its range of affected
 * clauses to `fl`.
 * 
 * This function does NOT require that `assume_subst()` has been called.
 * Instead, it pulls directly from the stored witness.
 * However, it skips a validity check that `assume_subst()` does perform.
 * 
 * @param lc The literal occurrence data for the formula.
 * @param[out] fl The place to write min/max clause to check. 
 */
void get_fl_clause_for_subst(srid_t line_num, lit_occ_t *lc, fl_clause_t *fl) {
  fl->first_clause = CLAUSE_ID_FROM_LINE_NUM(line_num) - 1;
  fl->last_clause = 0;

  int *witness_iter = get_witness_start(line_num);
  int *witness_end = get_witness_end(line_num);

  int seen_pivot_divider = 0;
  int pivot = witness_iter[0];
  int pivot_var = VAR_FROM_LIT(pivot);

  add_fl_for_lit(NEGATE_LIT(pivot), lc, fl);
  witness_iter++;

  for (; witness_iter < witness_end; witness_iter++) {
    int lit = *witness_iter;
    if (lit == WITNESS_TERM) break;
    int neg_lit = NEGATE_LIT(lit);
    int var = VAR_FROM_LIT(lit);

    if (!seen_pivot_divider) {
      if (lit == pivot) {
        seen_pivot_divider = 1;
      } else {
        add_fl_for_lit(neg_lit, lc, fl);
      }
    } else {
      witness_iter++;
      add_fl_for_lit(lit, lc, fl);
      add_fl_for_lit(neg_lit, lc, fl);
    }
  }
}

// Returns the `pivot` literal of the clause (if nonempty), or `-1` if empty.
int assume_negated_clause(srid_t clause_index, ullong gen) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "assume_negated_clause(): Clause %lld was out of bounds (%lld).",
    TO_DIMACS_CLAUSE(clause_index), formula_size);

  int *clause_iter = get_clause_start_unsafe(clause_index);
  int *clause_end = get_clause_end(clause_index);

  // Only store the pivot if the clause is nonempty
  int pivot = (clause_iter != clause_end) ? clause_iter[0] : -1;

  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    set_lit_for_alpha(NEGATE_LIT(lit), gen);
  }

  return pivot;
}

/**
 * @brief Assumes into the current truth assignment
 *        the negation of the clause when mapped under the substitution.
 * 
 * When performing a RAT check, we get to assume the negation of the RAT clause
 * `clause_index` (after mapping it under the current substitution)
 * into the current truth assignment. Syntactically, this looks like:
 * 
 *   `F /\ !C /\ !(D|s) |-1 \bot`
 * 
 * Note that since all CNF clauses are disjunctive, the negation of a clause
 * is the AND of the clause's negated unit literals.
 * 
 * To assume the negated mapped clause `D`, we loop through the literals of `D`
 * and map each literal `l` under the current substitution. We then add the
 * negation of the mapped literal to `alpha`.
 * 
 * If any literal evaluates to true under the substitution, or any mapped
 * literal evaluates to true under `alpha`, then `D` is either not
 * in `(F /\ C)|s` or it causes a trivial UP refutation, respectively.
 * Any mapped literal that evaluates to false under `alpha` is ignored,
 * since assuming it into `alpha` would have no effect.
 * 
 * @param clause_index The index of the clause to assume the negation of.
 * @param gen The generation/timestamp to set for assumed literals.
 * @return `SATISFIED_OR_MUL` if the clause is trivially satisfied/refuted,
 *         and `0` otherwise.
 */
int assume_negated_clause_under_subst(srid_t clause_index, ullong gen) {
  FATAL_ERR_IF(clause_index < 0 || clause_index > formula_size,
    "assume_neg_clause_under_subst(): Clause %lld was out of bounds (%lld).",
    TO_DIMACS_CLAUSE(clause_index), formula_size);
  
  int *clause_iter = get_clause_start_unsafe(clause_index);
  int *clause_end = get_clause_end(clause_index);
  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    int mapped_lit = map_lit_under_subst(lit);
    switch (mapped_lit) {
      case SUBST_FF: break; // Ignore the literal
      case SUBST_TT: return SATISFIED_OR_MUL;
      default:;
        int mapped_eval = peval_lit_under_alpha(mapped_lit);
        switch (mapped_eval) {
          case FF: break; // Ignore the literal
          case TT: return SATISFIED_OR_MUL;
          case UNASSIGNED: set_lit_for_alpha(NEGATE_LIT(mapped_lit), gen); break;
          default: log_fatal_err("Corrupted peval value: %d.", mapped_eval);
        }
    }
  }

  return 0;
}

// Evaluate the clause under the substitution.
// A return value of `SATISFIED_OR_MUL` means the clause is satisfied only.
int reduce_clause_under_subst(srid_t clause_index) {
  FATAL_ERR_IF(is_clause_deleted(clause_index),
    "Trying to reduce a deleted clause (%lld).",
    TO_DIMACS_CLAUSE(clause_index));

  uint id_mapped_lits = 0;
  uint falsified_lits = 0;
  int *iter = get_clause_start_unsafe(clause_index);
  int *end = get_clause_end(clause_index);
  int clause_size = end - iter;

  // Evaluate the literals under the substitution first
  // If the witness is a substitution, tautologies can be produced. But we don't
  // report those here, because when the clause is assumed into alpha, one of
  // the two literals will either be true, or assumed fresh and set the other to true.
  for (; iter < end; iter++) {
    int lit = *iter;
    int mapped_lit = map_lit_under_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT:
        return SATISFIED_OR_MUL;
      case SUBST_FF:
        falsified_lits++;
        break;
      default:
        if (mapped_lit == lit) {
          id_mapped_lits++;
        }
    }
  }

  if (falsified_lits == clause_size) {
    return CONTRADICTION;
  } else if (id_mapped_lits == clause_size) {
    return NOT_REDUCED;
  } else {
    return REDUCED;
  }
}

int reduce_clause_under_pivot(srid_t clause_index, int pivot) {
  FATAL_ERR_IF(is_clause_deleted(clause_index),
    "Trying to reduce supposed RAT clause %lld, but it has been deleted.",
    TO_DIMACS_CLAUSE(clause_index));

  int *iter = get_clause_start_unsafe(clause_index);
  int *end = get_clause_end(clause_index);
  int clause_size = end - iter;
  int negated_pivot = NEGATE_LIT(pivot);

  for (; iter < end; iter++) {
    int lit = *iter;
    if (lit == pivot) {
      return SATISFIED_OR_MUL;
    } else if (lit == negated_pivot) {
      if (clause_size == 1) {
        return CONTRADICTION;
      } else {
        return REDUCED; 
      }
    }
  }

  return NOT_REDUCED;
}

static srid_t move_min_forward(int lit, srid_t first, srid_t last) {
  // Scan forward until we find a non-deleted clause containing lit
  for (++first; first < last; first++) {
    if (!is_clause_deleted(first)) {
      // Check the clause for the literal
      int *clause_ptr = get_clause_start_unsafe(first);
      int *end_ptr = get_clause_end(first);
      for (; clause_ptr < end_ptr; clause_ptr++) {
        if (*clause_ptr == lit) {
          return first;
        }
      }
    }
  }

  return (is_clause_deleted(last)) ? -1 : last;
}

static srid_t move_max_backward(int lit, srid_t first, srid_t last) {
  // Scan backward until we find a non-deleted clause containing lit
  for (--last; last > first; last--) {
    if (!is_clause_deleted(last)) {
      // Check the clause for the literal
      int *clause_ptr = get_clause_start_unsafe(last);
      int *end_ptr = get_clause_end(last);
      for (; clause_ptr < end_ptr; clause_ptr++) {
        if (*clause_ptr == lit) {
          return last;
        }
      }
    }
  }

  return first;
}

void dbg_print_clause(srid_t clause_index) {
  if (is_clause_deleted(clause_index)) return;

  int *clause_iter = get_clause_start(clause_index);
  int *clause_end = get_clause_end(clause_index);
  log_raw(VL_NORMAL, "[%lld] ", TO_DIMACS_CLAUSE(clause_index));
  for (; clause_iter < clause_end; clause_iter++) {
    log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(*clause_iter));
  }
  log_raw(VL_NORMAL, "0\n"); 
}

void dbg_print_clause_under_alpha(srid_t clause_index) {
  log_raw(VL_NORMAL, "[%lld|a] ", TO_DIMACS_CLAUSE(clause_index));
  int *clause_iter = get_clause_start(clause_index);
  int *end = get_clause_end(clause_index);
  for (; clause_iter < end; clause_iter++) {
    int lit = *clause_iter;
    int mapped_lit = peval_lit_under_alpha(lit);
    switch (mapped_lit) {
      case TT: log_raw(VL_NORMAL, "TT "); break;
      case FF: log_raw(VL_NORMAL, "FF "); break;
      default: log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(mapped_lit));
    }
  }
  log_raw(VL_NORMAL, "0\n");
}

void dbg_print_clause_under_subst(srid_t clause_index) {
  log_raw(VL_NORMAL, "[%lld|w] ", TO_DIMACS_CLAUSE(clause_index));
  int *clause_iter = get_clause_start(clause_index);
  int *end = get_clause_end(clause_index);
  for (; clause_iter < end; clause_iter++) {
    int lit = *clause_iter;
    int mapped_lit = map_lit_under_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT: log_raw(VL_NORMAL, "TT "); break;
      case SUBST_FF: log_raw(VL_NORMAL, "FF "); break;
      default: log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(mapped_lit));
    }
  }
  log_raw(VL_NORMAL, "0\n");
}

void dbg_print_formula(void) {
  for (srid_t c = 0; c < formula_size; c++) {
    dbg_print_clause(c);
  }
}

void dbg_print_assignment(void) {
  log_raw(VL_NORMAL, "[DBG] Current assignment: ");
  for (int i = 0; i <= max_var; i++) {
    switch (peval_lit_under_alpha(i * 2)) {
      case TT:
        log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(i * 2));
        break;
      case FF:
        log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT((i * 2) + 1));
        break;
      default: break;
    }
  }
  log_raw(VL_NORMAL, "\n");
}

void dbg_print_subst(void) {
  log_raw(VL_NORMAL, "[DBG] Current substitution: ");
  // Do two passes to print the TT/FF first, then the mapped ones
  for (int i = 0; i <= max_var; i++) {
    int lit = i * 2;
    int mapped_lit = map_lit_under_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT:
        log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(lit));
        break;
      case SUBST_FF: 
        log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(NEGATE_LIT(lit)));
        break;
      default: break;
    }
  }

  for (int i = 0; i <= max_var; i++) {
    int lit = i * 2;
    int mapped_lit = map_lit_under_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT: break;
      case SUBST_FF: break;
      default:
        if (lit != mapped_lit) {
          // If the literals are swapped, print them once
          if (map_lit_under_subst(mapped_lit) == lit) {
            if (lit < mapped_lit) {
              log_raw(VL_NORMAL, "(%d %d) ",
                TO_DIMACS_LIT(lit), TO_DIMACS_LIT(mapped_lit));
            }
          } else {
            log_raw(VL_NORMAL, "(%d -> %d) ",
              TO_DIMACS_LIT(lit), TO_DIMACS_LIT(mapped_lit));
          }
        }
        break;
    }
  }

  log_raw(VL_NORMAL, "\n");
}

void dbg_print_witness(srid_t line_num) {
  int *witness_iter = get_witness_start(line_num);
  int *witness_end = get_witness_end(line_num);

  log_raw(VL_NORMAL, "[DBG] [line %lld] Witness: ", line_num + 1);
  for (; witness_iter < witness_end; witness_iter++) {
    int lit = *witness_iter;
    switch (lit) {
      case WITNESS_TERM: witness_iter = witness_end;          break;
      case SUBST_FF: log_raw(VL_NORMAL, "FF ");               break;
      case SUBST_TT: log_raw(VL_NORMAL, "TT ");               break;
      default: log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(lit)); break;
    }
  }

  log_raw(VL_NORMAL, "0\n");
}
