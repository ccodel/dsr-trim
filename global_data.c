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

#include "xmalloc.h"
#include "global_data.h"

/** Determines if the sign bit is set to mark a deleted clause. */
#define IS_DELETED_CLAUSE(x)      ((x) & MSB32)

/** Removes the sign bit from the clause index value to remove deletion info. */
#define CLAUSE_IDX(x)             ((x) & (~MSB32))

/** Sets the sign bit for the clause index value to logically delete it. */
#define DELETE_CLAUSE(x)          ((x) | MSB32)

// TODO: Instead of floating point, use numerator and denominator.
#define DELETION_GC_THRESHOLD     (0.3)

////////////////////////////////////////////////////////////////////////////////

int *lits_db = NULL;
int lits_db_size = 0;
int lits_db_alloc_size = 0;

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
static int lits_db_deleted_size = 0;

int *formula = NULL;
int formula_size = 0;
int formula_alloc_size = 0;

int *lits_first_clause = NULL;
int *lits_last_clause = NULL;

long *alpha = NULL;
long *subst_generations = NULL;
int *subst_mappings = NULL;
int alpha_subst_alloc_size = 0;
long alpha_generation = 0;
long subst_generation = 0;

int *witness = NULL;
int witness_size = 0;
int witness_alloc_size = 0;
int pivot = 0;
int new_clause_size = 0;
int subst_index = 0;

int min_clause_to_check = 0;
int max_clause_to_check = 0;

int max_var = 0;

////////////////////////////////////////////////////////////////////////////////

int intcompare (const void *a, const void *b) {
  return (*(int*)a - *(int*)b); 
}

int absintcompare (const void *a, const void *b) {
  int ia = *(int*)a;
  int ib = *(int*)b;
  return (ABS(ia) - ABS(ib)); 
}

// TODO: determine how to mark functions as inline wrt header files. Profile later?

void init_global_data(int num_clauses, int num_vars) {
  // TODO: Refine multipliers later
  lits_db_alloc_size = num_vars * 10;
  formula_alloc_size = num_clauses * 2;
  alpha_subst_alloc_size = num_vars * 10;
  max_var = num_vars; // TODO: Should increment based on seen, or on CNF header?

  lits_db_size = 0;
  formula_size = 0;

  lits_db = xmalloc(lits_db_alloc_size * sizeof(int));
  formula = xmalloc(formula_alloc_size * sizeof(int));
  formula[0] = 0;

  lits_first_clause = xmalloc(alpha_subst_alloc_size * sizeof(int));
  lits_last_clause = xmalloc(alpha_subst_alloc_size * sizeof(int));
  memset(lits_first_clause, 0xff, alpha_subst_alloc_size * sizeof(int));
  memset(lits_last_clause, 0xff, alpha_subst_alloc_size * sizeof(int));

  alpha = xcalloc(alpha_subst_alloc_size, sizeof(long));
  subst_generations = xcalloc(alpha_subst_alloc_size, sizeof(long));
  subst_mappings = xmalloc(alpha_subst_alloc_size * sizeof(int));

  witness_alloc_size = max_var * 2;
  witness_size = 0;
  witness = xmalloc(witness_alloc_size * sizeof(int));
}

// Assumes that VAR_FROM_LIT(lit) < alpha_subst_size
inline void set_lit_for_alpha(int lit, long gen) {
  if (IS_POS_LIT(lit)) {
    alpha[VAR_FROM_LIT(lit)] = gen;
  } else {
    alpha[VAR_FROM_LIT(lit)] = -gen;
  }
}

// Compares against alpha_generation
inline peval_t peval_lit_under_alpha(int lit) {
  long gen = alpha[VAR_FROM_LIT(lit)];
  if (ABS(gen) >= alpha_generation) {
    return ((gen >= alpha_generation) ^ (IS_POS_LIT(lit))) ? FF : TT;
  } else {
    return UNASSIGNED;
  }
}

inline void set_mapping_for_subst(int lit, int lit_mapping, long gen) {
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
  long gen = subst_generations[var];
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
static inline void update_first_last(int lit) {
  lits_last_clause[lit] = formula_size;
  if (lits_first_clause[lit] == -1) {
    lits_first_clause[lit] = formula_size;
  } 
}

void insert_lit(int lit) {
  // Insert the literal into the literal database
  RESIZE_ARR(lits_db, lits_db_alloc_size, lits_db_size, sizeof(int));
  lits_db[lits_db_size++] = lit;

  // Resize the other var-indexed arrays if new max would exceed allocated size
  int var = VAR_FROM_LIT(lit);
  max_var = MAX(max_var, var);
  if (max_var >= alpha_subst_alloc_size) {
    int old_size = alpha_subst_alloc_size;
    alpha_subst_alloc_size = RESIZE(max_var);
    alpha = xrealloc(alpha, alpha_subst_alloc_size * sizeof(long));
    subst_generations = xrealloc(subst_generations, alpha_subst_alloc_size * sizeof(long));
    subst_mappings = xrealloc(subst_mappings, alpha_subst_alloc_size * sizeof(int));
    lits_first_clause = xrealloc(lits_first_clause, alpha_subst_alloc_size * sizeof(int));
    lits_last_clause = xrealloc(lits_last_clause, alpha_subst_alloc_size * sizeof(int));

    // Set to default values in the new allocated regions
    int added_size = alpha_subst_alloc_size - old_size;
    memset(alpha + old_size, 0, added_size * sizeof(long));
    memset(subst_generations + old_size, 0, added_size * sizeof(long));
    memset(lits_first_clause + old_size, 0xff, added_size * sizeof(int));
    memset(lits_last_clause + old_size, 0xff, added_size * sizeof(int));
  }

  update_first_last(lit);
}

// Not inlined, and used as helper for insert_lit() because common operation.
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
    alpha = xrealloc(alpha, alpha_subst_alloc_size * sizeof(long));
    subst_generations = xrealloc(subst_generations, alpha_subst_alloc_size * sizeof(long));
    subst_mappings = xrealloc(subst_mappings, alpha_subst_alloc_size * sizeof(int));
    lits_first_clause = xrealloc(lits_first_clause, alpha_subst_alloc_size * sizeof(int));
    lits_last_clause = xrealloc(lits_last_clause, alpha_subst_alloc_size * sizeof(int));

    // Set to default values in the new allocated regions
    int added_size = alpha_subst_alloc_size - old_size;
    memset(alpha + old_size, 0, added_size * sizeof(long));
    memset(subst_generations + old_size, 0, added_size * sizeof(long));
    memset(lits_first_clause + old_size, 0xff, added_size * sizeof(int));
    memset(lits_last_clause + old_size, 0xff, added_size * sizeof(int));
  }
}

void insert_clause(void) {
  // We increment formula_size first to ensure that one past the last entry is allocated
  // We use this to store the clause_index for the incoming clause
  formula_size++;  // Cap off the current clause and prepare the next one
  RESIZE_ARR(formula, formula_alloc_size, formula_size, sizeof(int));
  formula[formula_size] = lits_db_size;
}

void insert_clause_first_last_update(void) {
  for (int i = formula[formula_size]; i < lits_db_size; i++) {
    update_first_last(lits_db[i]);
  }

  insert_clause();
}

inline int is_clause_deleted(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "is_clause_deleted: Clause index was out of bounds.");
  return IS_DELETED_CLAUSE(formula[clause_index]);
}

/** Copies memory to an address lower in the address space.
 * 
 *  Checks if the regions overlap to choose `memcpy` or `memmove`.
 */
static inline void memshift(void *restrict dst, const void *restrict src, size_t n) {
  if (((char *) dst) + n < ((char *) src)) {
    memcpy(dst, src, n);
  } else {
    memmove(dst, src, n);
  }
}

static inline void gc_lits_db(void) {
  if (lits_db_deleted_size > DELETION_GC_THRESHOLD * lits_db_size) {
    int insert_index = 0;
    int clause_idx;
    int next_clause_idx = formula[0]; // First loop takes value of next_clause_ptr
    for (int i = 0; i < formula_size; i++) {
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
          int size = CLAUSE_IDX(next_clause_idx) - clause_idx;
          memshift(lits_db + insert_index, lits_db + clause_idx, size * sizeof(int));
          insert_index += size;
        }
      }
    }

    // Finally, update the place to put a new clause, moving "pending" literals if any
    // Lemma: the final clause is not deleted
    clause_idx = next_clause_idx;
    formula[formula_size] = insert_index;
    int size = lits_db_size - clause_idx;
    memshift(lits_db + insert_index, lits_db + clause_idx, size * sizeof(int));
    lits_db_size = insert_index + size;
    lits_db_deleted_size = 0;
  }
}

void delete_clause(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "delete_clause: Clause index was out of bounds.");
  int clause_ptr = formula[clause_index];
  if (IS_DELETED_CLAUSE(clause_ptr)) {
    PRINT_ERR_AND_EXIT("The clause was already deleted.");
  } else {
    // TODO: Could break if delete clause just added(?)
    int next_clause_ptr = CLAUSE_IDX(formula[clause_index + 1]);
    lits_db_deleted_size += next_clause_ptr - clause_ptr;
    formula[clause_index] = DELETE_CLAUSE(clause_ptr);
    gc_lits_db(); // If we deleted too much from `lits_db`, garbage collect
  }
}

inline int *get_clause_start_unsafe(int clause_index) {
  return lits_db + formula[clause_index];
}

inline int *get_clause_start(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "get_clause_start: Clause index was out of bounds.");
  return lits_db + CLAUSE_IDX(formula[clause_index]);
}

// TODO: What should this return for the new clause, if not yet added?
inline int get_clause_size(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "get_clause_size: Clause index was out of bounds.");
  if (clause_index == formula_size) {
    return lits_db_size - CLAUSE_IDX(formula[clause_index]);
  } else {
    return CLAUSE_IDX(formula[clause_index + 1]) - CLAUSE_IDX(formula[clause_index]);
  }
}

// Assumes the substitution witness, if it exists. If it doesn't, it uses
// the pivot (the first literal in the clause to be added).
// The clause must be nonempty.
// Updates the min/max_clause_check_to_check
void assume_subst(long gen) {
  // Set the pivot, just in case the witness is empty
  set_mapping_for_subst(pivot, SUBST_TT, gen);

  // We have to check clauses that are reduced by the negation of the pivot
  int neg_pivot = NEGATE_LIT(pivot);
  min_clause_to_check = MIN(min_clause_to_check, lits_first_clause[neg_pivot]);
  max_clause_to_check = MAX(max_clause_to_check, lits_last_clause[neg_pivot]);
  for (int i = 1; i < witness_size; i++) {
    if (i < subst_index) {
      set_mapping_for_subst(witness[i], SUBST_TT, gen);
    } else {
      set_mapping_for_subst(witness[i], witness[i + 1], gen);
      i++;
    }
  }
}

void assume_negated_clause(int clause_index, long gen) {
  PRINT_ERR_AND_EXIT_IF(clause_index < 0 || clause_index > formula_size,
    "assume_negated_clause: Clause index was out of bounds.");

  if (clause_index == formula_size) {
    for (int i = formula[formula_size]; i < lits_db_size; i++) {
      int lit = lits_db[i];
      set_lit_for_alpha(NEGATE_LIT(lit), gen);
    }
  } else {
    int *clause_ptr = get_clause_start(clause_index);
    int *end = get_clause_start(clause_index + 1);
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
int assume_negated_clause_under_subst(int clause_index, long gen) {
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
int reduce_subst_mapped(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(is_clause_deleted(clause_index),
    "Trying to unit propagate on a deleted clause.");

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
  int first = lits_first_clause[lit];
  int last = lits_last_clause[lit];
  int found_new = 0;

  if (first == -1) return;  // If the literal isn't in any clause, nothing to do

  if (is_clause_deleted(first)) {
    // Scan forward until we find a non-deleted clause containing lit
    for (first++; first < last; first++) {
      if (!is_clause_deleted(first)) {
        // Check the clause for the literal
        int *clause_ptr = get_clause_start(first);
        int *end_ptr = get_clause_start(first + 1);
        for (; clause_ptr < end_ptr; clause_ptr++) {
          // TODO: Assumes clauses are sorted. Call quicksort() elsewhere?
          if (*clause_ptr == lit) {
            lits_first_clause[lit] = first;
            found_new = 1;
            break;
          } else if (*clause_ptr > lit) {
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
    for (last--; last > first; last--) {
      if (!is_clause_deleted(last)) {
        // Check the clause for the literal
        int *clause_ptr = get_clause_start(last);
        int *end_ptr = get_clause_start(last + 1);
        for (; clause_ptr < end_ptr; clause_ptr++) {
          if (*clause_ptr == lit) {
            lits_last_clause[lit] = last;
            found_new = 1;
            break;
          } else if (*clause_ptr > lit) {
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