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

#ifdef LONGTYPE
/** Determines if the sign bit is set to mark a deleted clause. */
#define IS_DELETED_CLAUSE(x)      ((x) & MSB64)

/** Removes the sign bit from the clause index value to remove deletion info. */
#define CLAUSE_IDX(x)             ((x) & (~MSB64))

/** Sets the sign bit for the clause index value to logically delete it. */
#define DELETE_CLAUSE(x)          ((x) | MSB64)
#else
/** Determines if the sign bit is set to mark a deleted clause. */
#define IS_DELETED_CLAUSE(x)      ((x) & MSB32)

/** Removes the sign bit from the clause index value to remove deletion info. */
#define CLAUSE_IDX(x)             ((x) & (~MSB32))

/** Sets the sign bit for the clause index value to logically delete it. */
#define DELETE_CLAUSE(x)          ((x) | MSB32)
#endif

// TODO: Instead of floating point, use numerator and denominator.
#define DELETION_GC_THRESHOLD     (0.3)

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

srid_t *lits_first_clause = NULL;
srid_t *lits_last_clause = NULL;

llong *alpha = NULL;
llong *subst_generations = NULL;
int *subst_mappings = NULL;
int alpha_subst_alloc_size = 0;
llong alpha_generation = 0;
llong subst_generation = 0;

range_array_t witnesses;

int pivot = 0;

srid_t min_clause_to_check = 0;
srid_t max_clause_to_check = 0;

int new_clause_size = 0;
int max_var = 0;
int derived_empty_clause = 0;

////////////////////////////////////////////////////////////////////////////////

int intcmp(const void *a, const void *b) {
  return (*(int*)a - *(int*)b); 
}

int absintcmp(const void *a, const void *b) {
  int ia = *(int*)a;
  int ib = *(int*)b;
  return (ABS(ia) - ABS(ib)); 
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
  // TODO: Refine multipliers later
  lits_db_alloc_size = num_cnf_clauses * 10;
  formula_alloc_size = num_cnf_clauses * 2;
  alpha_subst_alloc_size = num_cnf_vars * 10;
  max_var = num_cnf_vars; // TODO: Should increment based on seen, or on CNF header?

  lits_db_size = 0;
  formula_size = 0;

  lits_db = xmalloc(lits_db_alloc_size * sizeof(int));
  formula = xmalloc(formula_alloc_size * sizeof(srid_t));
  formula[0] = 0;

  lits_first_clause = xrealloc_memset(lits_first_clause,
    0, alpha_subst_alloc_size * sizeof(srid_t), 0xff);
  lits_last_clause = xrealloc_memset(lits_last_clause,
    0, alpha_subst_alloc_size * sizeof(srid_t), 0xff);

  alpha = xcalloc(alpha_subst_alloc_size, sizeof(llong));
  subst_generations = xcalloc(alpha_subst_alloc_size, sizeof(llong));
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
    default: PRINT_ERR_AND_EXIT("Unknown parsing strategy.");
  }
}

// Assumes that VAR_FROM_LIT(lit) < alpha_subst_size
inline void set_lit_for_alpha(int lit, llong gen) {
  if (IS_POS_LIT(lit)) {
    alpha[VAR_FROM_LIT(lit)] = gen;
  } else {
    alpha[VAR_FROM_LIT(lit)] = -gen;
  }
}

// Compares against alpha_generation
inline peval_t peval_lit_under_alpha(int lit) {
  llong gen = alpha[VAR_FROM_LIT(lit)];
  if (ABS(gen) >= alpha_generation) {
    return ((gen >= alpha_generation) ^ (IS_POS_LIT(lit))) ? FF : TT;
  } else {
    return UNASSIGNED;
  }
}

inline void set_mapping_for_subst(int lit, int lit_mapping, llong gen) {
  int var = VAR_FROM_LIT(lit);
  subst_generations[var] = gen;
  if (IS_POS_LIT(lit)) {
    subst_mappings[var] = lit_mapping;
  } else {
    subst_mappings[var] = NEGATE_LIT(lit_mapping);
  }
}

// Returns the lit value of subst(lit). Can return SUBST_TT/_FF.
// Compares against subst_generation.
inline int get_lit_from_subst(int lit) {
  int var = VAR_FROM_LIT(lit);
  llong gen = subst_generations[var];
  if (gen >= subst_generation) {
    // Equivalently,
    // (IS_POS_LIT(lit)) ? sm[V(lit)] : NEGATE_LIT(sm[V(lit)]);
    return (subst_mappings[var]) ^ (IS_NEG_LIT(lit));
  } else {
    // TODO: Or could we return lit here instead?
    return SUBST_UNASSIGNED;
  }
}

// Updates the first and last appearances of this literal
static inline void update_first_last(int lit, srid_t clause_index) {
  lits_last_clause[lit] = clause_index;
  if (lits_first_clause[lit] == -1) {
    lits_first_clause[lit] = clause_index;
  }
}

void insert_lit(int lit) {
  insert_lit_no_first_last_update(lit);
  update_first_last(lit, formula_size);
}

// Updates max_var and resizes global_data arrays that depend on max_var.
void insert_lit_no_first_last_update(int lit) {
  // Insert the literal into the literal database
  RESIZE_ARR(lits_db, lits_db_alloc_size, lits_db_size, sizeof(int));
  lits_db[lits_db_size++] = lit;

  // Resize the other var-indexed arrays if new max would exceed allocated size
  int var = VAR_FROM_LIT(lit);
  max_var = MAX(max_var, var);
  if (max_var >= alpha_subst_alloc_size) {
    int old_size = alpha_subst_alloc_size;
    alpha_subst_alloc_size = RESIZE(max_var);
    alpha = xrecalloc(alpha, old_size * sizeof(llong),
      alpha_subst_alloc_size * sizeof(llong));
    subst_generations = xrecalloc(subst_generations, old_size * sizeof(llong),
      alpha_subst_alloc_size * sizeof(llong));
    lits_first_clause = xrealloc_memset(lits_first_clause,
      old_size * sizeof(srid_t), alpha_subst_alloc_size * sizeof(srid_t), 0xff);
    lits_last_clause = xrealloc_memset(lits_last_clause,
      old_size * sizeof(srid_t), alpha_subst_alloc_size * sizeof(srid_t), 0xff);
    subst_mappings = xrealloc(subst_mappings, alpha_subst_alloc_size * sizeof(int));
  }
}

void perform_clause_first_last_update(srid_t clause_index) {
  int *clause = get_clause_start_unsafe(clause_index);
  int clause_size = get_clause_size(clause_index);

  for (int i = 0; i < clause_size; i++) {
    update_first_last(clause[i], clause_index);
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

/** @brief Commits the current set of uncommitted literals to a new
 * formula clause, and also updates the first/last clause index for
 * each literal in the clause.
 * 
 * The global arrays `lits_first_clause` and `lits_last_clause` are indexed
 * by literal and track the first/last clause index that that literal
 * appears in. This function runs over the uncommitted literals and
 * updates those values before calling `commit_clause()`.
 */
void commit_clause_with_first_last_update(void) {
  perform_clause_first_last_update(formula_size);
  commit_clause();
}

/** @brief Uncommits the final clause from the formula.
 * 
 * The literals in `lits_db` are not deleted. Rather, the `formula_size`
 * is decreased by 1, and for each literal in the uncommitted clause,
 * their `lits_last_clause` value are decreased to the clause before this
 * one that contains the literal. If no other clause contains the literal,
 * then the value is set to -1.
 * 
 * The caller must ensure that no clauses are committed and no literals
 * are added after this function * returns, and that there are currently
 * no uncommitted literals.
 * 
 * TODO: question: what should we do about clauses that haven't been marked
 * yet in dsr-trim when doing backwards checking, since we might not want
 * to check those clauses that ultimately won't be used in the final proof?
 */
void uncommit_clause_with_first_last_update(void) {
  // Reverse direction of `commit_clause_w_f_l_update()`.
  formula_size--;
  int *clause = get_clause_start_unsafe(formula_size);
  int clause_size = get_clause_size(formula_size);

  for (int i = 0; i < clause_size; i++) {
    // TODO: efficiency for finding the clause before this one that
    // mentions the literal
    // Use a char array to mark (1), then scan backwards?
  }
}

inline int is_clause_deleted(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "is_clause_deleted: Clause index was out of bounds.");
  return IS_DELETED_CLAUSE(formula[clause_index]);
}

/** Copies memory to an address lower in the address space.
 * 
 *  Checks if the regions overlap to choose `memcpy` or `memmove`.
 */
static inline void memshift(void *restrict dst, const void *restrict src, size_t n) {
  // TODO: Technically suffers from overflow bug
  if (((char *) dst) + n < ((char *) src)) {
    memcpy(dst, src, n);
  } else {
    memmove(dst, src, n);
  }
}

static inline void gc_lits_db(void) {
  if (lits_db_deleted_size > DELETION_GC_THRESHOLD * lits_db_size) {
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
          memshift(lits_db + insert_index, lits_db + clause_idx, size * sizeof(int));
          insert_index += size;
        }
      }
    }

    // Finally, update the place to put a new clause, moving "pending" literals if any
    // Lemma: the final clause is not deleted
    clause_idx = next_clause_idx;
    formula[formula_size] = insert_index;
    srid_t size = lits_db_size - clause_idx;
    memshift(lits_db + insert_index, lits_db + clause_idx, size * sizeof(int));
    lits_db_size = insert_index + size;
    lits_db_deleted_size = 0;
  }
}

void delete_clause(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "delete_clause: Clause index was out of bounds.");
  srid_t clause_ptr = formula[clause_index];
  if (IS_DELETED_CLAUSE(clause_ptr)) {
    PRINT_ERR_AND_EXIT("The clause was already deleted.");
  } else {
    // TODO: Could break if delete clause just added(?)
    srid_t next_clause_ptr = CLAUSE_IDX(formula[clause_index + 1]);
    lits_db_deleted_size += next_clause_ptr - clause_ptr;
    formula[clause_index] = DELETE_CLAUSE(clause_ptr);
    gc_lits_db(); // If we deleted too much from `lits_db`, garbage collect
  }
}

inline int *get_clause_start_unsafe(srid_t clause_index) {
  return lits_db + formula[clause_index];
}

inline int *get_clause_start(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "get_clause_start: Clause index was out of bounds.");
  return lits_db + CLAUSE_IDX(formula[clause_index]);
}

// TODO: What should this return for the new clause, if not yet added?
inline int get_clause_size(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "get_clause_size: Clause index was out of bounds.");
  if (clause_index == formula_size) {
    return lits_db_size - CLAUSE_IDX(formula[clause_index]);
  } else {
    return CLAUSE_IDX(formula[clause_index + 1]) - CLAUSE_IDX(formula[clause_index]);
  }
}

static inline int *get_witness_start(srid_t line_num) {
  if (p_strategy == PS_EAGER) {
    return ((int *) ra_get_range_start(&witnesses, line_num));
  } else {
    return ((int *) ra_get_range_start(&witnesses, 0));
  }
}

static inline int *get_witness_end(srid_t line_num) {
  if (p_strategy == PS_EAGER) {
    return ((int *) ra_get_range_start(&witnesses, line_num + 1));
  } else {
    return ((int *) ra_get_range_start(&witnesses, 1));
  }
}

static void set_min_and_max_clause_to_check(int lit) {
  update_first_last_clause(lit);
  if (lits_first_clause[lit] != -1) {
    min_clause_to_check = MIN(min_clause_to_check, lits_first_clause[lit]); 
    max_clause_to_check = MAX(max_clause_to_check, lits_last_clause[lit]);
  }
}

/**
 * @brief Moves the substitution mappings into `subst`. Sets the values for
 *        `min/max_clause_to_check`.
 * 
 * If the witness is empty, it uses the pivot literal (the first literal
 * of the candidate clause). The caller should ensure that `pivot` is set
 * before calling this function.
 * 
 * @param line_id The 0-indexed line ID of the substitution witness.
 *  If the parsing strategy is `PS_EAGER`, this ID corresponds to the
 *  range array index in `witnesses`. Otherwise, the line ID is ignored.
 */
void assume_subst(srid_t line_num) {
  min_clause_to_check = formula_size - 1;
  max_clause_to_check = 0;
  char seen_pivot_divider = 0;
  const int pivot_var = VAR_FROM_LIT(pivot);

  // Set the pivot, just in case the witness is empty
  set_mapping_for_subst(pivot, SUBST_TT, subst_generation);
  set_min_and_max_clause_to_check(NEGATE_LIT(pivot));

  int *witness_iter = get_witness_start(line_num) + 1;
  int *witness_end = get_witness_end(line_num);

  // For all other literals l in the witness
  // 1. Check that var(l) hasn't been set yet (compare gen against subst_generation)
  // 2. Set its mapping
  for (; witness_iter < witness_end; witness_iter++) {
    int lit = *witness_iter;
    if (lit == WITNESS_TERM) break;
    int neg_lit = NEGATE_LIT(lit);
    int var = VAR_FROM_LIT(lit);

    // Error if we have already set a variable in the substitution.
    // This ensures no variable appears twice.
    // Note that the pivot can be re-set in the substitution portion
    PRINT_ERR_AND_EXIT_IF(
      subst_generations[var] == subst_generation && var != pivot_var,
      "Literal in witness was already set.");

    if (!seen_pivot_divider) {
      if (lit == pivot) {
        seen_pivot_divider = 1; // Skip the pivot divider
      } else {
        set_mapping_for_subst(lit, SUBST_TT, subst_generation);
        set_min_and_max_clause_to_check(neg_lit);
      }
    } else {
      witness_iter++;
      set_mapping_for_subst(lit, *witness_iter, subst_generation);
      set_min_and_max_clause_to_check(lit);
      set_min_and_max_clause_to_check(neg_lit);
    }
  }
}

void assume_negated_clause(srid_t clause_index, llong gen) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "assume_negated_clause: Clause index was out of bounds.");

  if (clause_index == formula_size) {
    int i = formula[formula_size];

    // Only set the pivot if the clause is non-empty
    if (i < lits_db_size) {
      pivot = lits_db[i];
    }

    for (int i = formula[formula_size]; i < lits_db_size; i++) {
      int lit = lits_db[i];
      set_lit_for_alpha(NEGATE_LIT(lit), gen);
    }
  } else {
    int *clause_ptr = get_clause_start(clause_index);
    int *end = get_clause_start(clause_index + 1);

    if (clause_ptr < end) {
      pivot = *clause_ptr;
    }

    for (; clause_ptr < end; clause_ptr++) {
      set_lit_for_alpha(NEGATE_LIT(*clause_ptr), gen);
    }
  }
}

// Assumes the negation of the clause under the substitution.
// As the negated literals are read in, they are evaluated against alpha.
// If the clause is satisfied by alpha, then the assumption stops.
// Returns SATISFIED_OR_MUL if the clause is satisfied by alpha (or the subst),
// and 0 otherwise.
int assume_negated_clause_under_subst(srid_t clause_index, llong gen) {
  // TODO: Excludes the clause to be added (at formula_size)
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index >= formula_size,
    "assume_negated_clause_under_subst: Clause index was out of bounds.");
  
  int *clause_ptr = get_clause_start(clause_index);
  int *end = get_clause_start(clause_index + 1);
  for (; clause_ptr < end; clause_ptr++) {
    int lit = *clause_ptr;
    int mapped_lit = get_lit_from_subst(lit);
    // Evaluate the lit under the substitution, assuming it won't be satisfied
    switch (mapped_lit) {
      case SUBST_TT: return SATISFIED_OR_MUL;
      case SUBST_FF: break; // Ignore the literal
      case SUBST_UNASSIGNED: // TODO: See note in get_lit_from_subst
        mapped_lit = lit;
      default:
        // Now evaluate the mapped literal under alpha. If it's unassigned, set it
        switch (peval_lit_under_alpha(mapped_lit)) {
          case FF: break; // Ignore the literal
          case TT: return SATISFIED_OR_MUL;
          case UNASSIGNED: set_lit_for_alpha(NEGATE_LIT(mapped_lit), gen); break;
          default: PRINT_ERR_AND_EXIT("Corrupted peval value.");
        }
    }
  }

  return 0;
}

// Evaluate the clause under the substitution. SATISFIED_OR_MUL is satisfied only.
int reduce_subst_mapped(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(is_clause_deleted(clause_index),
    "Trying to apply substitution reduction on a deleted clause.");

  int id_mapped_lits = 0, falsified_lits = 0;
  int *start = get_clause_start(clause_index);
  int *end = get_clause_start(clause_index + 1);
  int size = end - start;

  // Evaluate the literals under the substitution first
  // If the witness is a substitution, tautologies can be produced. But we don't
  // report those here, because when the clause is assumed into alpha, one of
  // the two literals will either be true, or assumed fresh and set the other to true.
  for (; start < end; start++) {
    int lit = *start;
    int mapped_lit = get_lit_from_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT: return SATISFIED_OR_MUL;
      case SUBST_FF: falsified_lits++; break;
      case SUBST_UNASSIGNED: mapped_lit = lit;
      default:
        if (mapped_lit == lit) {
          id_mapped_lits++;
        }
    }
  }

  if (falsified_lits == size) {
    return CONTRADICTION;
  } else if (id_mapped_lits == size) {
    return NOT_REDUCED;
  } else {
    return REDUCED;
  }
}

void update_first_last_clause(int lit) {
  srid_t first = lits_first_clause[lit];
  srid_t last = lits_last_clause[lit];
  int found_new = 0;

  if (first == -1) return;  // If the literal isn't in any clause, nothing to do

  if (is_clause_deleted(first)) {
    // Scan forward until we find a non-deleted clause containing lit
    for (++first; first <= last; first++) {
      if (!is_clause_deleted(first)) {
        // Check the clause for the literal
        int *clause_ptr = get_clause_start(first);
        int *end_ptr = get_clause_start(first + 1);
        for (; clause_ptr < end_ptr; clause_ptr++) {
          // TODO: For lsr-check, clauses are sorted. Add a sorted flag here?
          if (*clause_ptr == lit) {
            lits_first_clause[lit] = first;
            found_new = 1;
            break;
          }
        }
      
        if (found_new) break;
      }
    }

    // If after going through all clauses, we don't find a non-deleted clause containing lit,
    // then all its clauses have been deleted. Reset to -1.
    if (!found_new) {
      lits_first_clause[lit] = -1;
      lits_last_clause[lit] = -1;
      return;
    }
  }

  // Lemma: first now points at a non-deleted clause containing lit
  if (first == last) return; // Ensure we can scan backwards

  // Now scan backwards to find the last clause containing lit
  if (is_clause_deleted(last)) {
    found_new = 0;
    // Scan backward until we find a non-deleted clause containing lit
    for (--last; last > first; last--) {
      if (!is_clause_deleted(last)) {
        // Check the clause for the literal
        int *clause_ptr = get_clause_start(last);
        int *end_ptr = get_clause_start(last + 1);
        for (; clause_ptr < end_ptr; clause_ptr++) {
          // TODO: Clauses are sorted? here too.
          if (*clause_ptr == lit) {
            lits_last_clause[lit] = last;
            found_new = 1;
            break;
          }
        }

        if (found_new) break;
      }
    }

    if (!found_new) {
      lits_last_clause[lit] = first;
    }
  }
}