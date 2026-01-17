/**
 * @file lit_occ.c
 * @brief Tracks the number of times and the clauses that literals occur in.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-12-11
 */

#include <string.h>

#include "global_data.h"
#include "lit_occ.h"
#include "logger.h"
#include "xmalloc.h"

#define MIN_LITS_CLAUSES_INNER_ARRAY_SIZE   (4)

#define START_IDX(l, lit)           (l->lits_clauses[lit].start_idx)
#define END_IDX(l, lit)             (l->lits_clauses[lit].end_idx)
#define END_IDX_INCLUSIVE(l, lit)   (END_IDX(l, lit) - 1)
#define SIZE_IDX(l, lit)            (l->lits_clauses[lit].size)

#define CLAUSES(l, lit)             (l->lits_clauses[lit].clauses)
#define CLAUSE_AT_START_IDX(l, lit) (CLAUSES(l, lit)[START_IDX(l, lit)])
#define CLAUSE_AT_END_IDX(l, lit)   (CLAUSES(l, lit)[END_IDX_INCLUSIVE(l, lit)])
#define CLAUSE_AT_SIZE_IDX(l, lit)  (CLAUSES(l, lit)[l->lits_clauses[lit].size - 1])

#ifndef FREE_IF_NOT_NULL
#define FREE_IF_NOT_NULL(ptr)   \
  if ((ptr) != NULL) {                    \
    xfree(ptr);                           \
  }
#endif

static void lc_map_init(lc_map_t *m) {
  memset(m, 0, sizeof(lc_map_t));
}

static void lc_map_destroy(lc_map_t *m) {
  if (m->clauses != NULL) {
    xfree(m->clauses);
  }

  memset(m, 0, sizeof(lc_map_t));
}

static void lc_map_realloc(lc_map_t *m) {
  srid_t old_size = m->alloc_size;
  m->alloc_size = (m->alloc_size == 0) ? MIN_LITS_CLAUSES_INNER_ARRAY_SIZE
                                      : RESIZE(m->alloc_size);
  m->clauses = xrealloc(m->clauses, m->alloc_size * sizeof(srid_t));
}

/**
 * @brief Initializes the `lit_occ_t` structure.
 * 
 * Doesn't allocate memory. To allocate memory, call an `add_formula` function.
 * 
 * Memory gets leaked if `lit_occ_init()` is called twice without an
 * intervening call to `lit_occ_destroy()`.
 */
void lit_occ_init(lit_occ_t *l) {
  memset(l, 0, sizeof(lit_occ_t));
}

/**
 * @brief Destroys the `lit_occ_t` structure, freeing all allocated memory.
 * 
 * Assumes that `lit_occ_init()` was called first. Undefined behavior otherwise.
 */
void lit_occ_destroy(lit_occ_t *l) {
  FREE_IF_NOT_NULL(l->lits_occurrences);
  FREE_IF_NOT_NULL(l->lits_first_last_clauses);

  if (l->lits_clauses != NULL) {
    for (int i = 0; i < l->alloc_size; i++) {
      FREE_IF_NOT_NULL(l->lits_clauses[i].clauses);
    }

    xfree(l->lits_clauses);
  }

  lit_occ_init(l);
}

// Allocates memory for `lits_clauses` if `with_lits_clauses` is set.
static void lit_occ_realloc_impl(lit_occ_t *l, int with_lits_clauses) {
  // Add extra padding if a higher `max_var` was parsed
  int mult = (l->alloc_size == 0) ? 2 : 3;
  int old_size = l->alloc_size;
  l->alloc_size = (max_var + 1) * mult;
  
  l->lits_occurrences = xrecalloc(l->lits_occurrences,
    old_size * sizeof(srid_t), l->alloc_size * sizeof(srid_t));
  l->lits_first_last_clauses = xrealloc_memset(l->lits_first_last_clauses,
    old_size * sizeof(fl_clause_t), l->alloc_size * sizeof(fl_clause_t), 0xff);

  if (with_lits_clauses) {
    l->lits_clauses = xrecalloc(l->lits_clauses,
      old_size * sizeof(lc_map_t), l->alloc_size * sizeof(lc_map_t));
  }
}

static void lit_occ_realloc_no_clause_mappings(lit_occ_t *l) {
  lit_occ_realloc_impl(l, 0);
}

static void lit_occ_realloc_with_clause_mappings(lit_occ_t *l) {
  lit_occ_realloc_impl(l, 1);
}

static void lit_occ_realloc(lit_occ_t *l) {
  if (l->lits_clauses == NULL) {
    lit_occ_realloc_no_clause_mappings(l);
  } else {
    lit_occ_realloc_with_clause_mappings(l);
  }
}

// Stores occurrence data (but not literal-clause mapping data) for the clause.
// Assumes that `clause_index` is not deleted in the formula.
static void store_clause_occurrences(lit_occ_t *l, srid_t clause_index) {
  if (is_clause_deleted(clause_index)) return;

  int *clause_ptr = get_clause_start_unsafe(clause_index);
  int *end_ptr = get_clause_end(clause_index);
  for (; clause_ptr < end_ptr; clause_ptr++) {
    int lit = *clause_ptr;
    l->lits_occurrences[lit]++;

    if (l->lits_occurrences[lit] == 1) {
      l->lits_first_last_clauses[lit].first_clause = clause_index;
      l->lits_first_last_clauses[lit].last_clause = clause_index;
    } else {
      SET_MIN_LEFT(l->lits_first_last_clauses[lit].first_clause, clause_index);
      SET_MAX_LEFT(l->lits_first_last_clauses[lit].last_clause, clause_index);
    }
  }
}

// Stores occurrences and f/l clauses in `l` by looping across the formula.
// Assumes that the `alloc()` functions have already been called.
// Assumes that `max_var` hasn't grown in the intervening time.
// `until_clause` is exclusive.
static void store_formula_occurrences(lit_occ_t *l, srid_t until_clause) {
  for (srid_t c = 0; c < until_clause; c++) {
    store_clause_occurrences(l, c);
  }
}

// Assumes that the clause is not deleted in the formula.
static void store_clause_mapping(lit_occ_t *l, srid_t clause_index) {
  if (is_clause_deleted(clause_index)) return;

  int *clause_ptr = get_clause_start_unsafe(clause_index);
  int *end_ptr = get_clause_end(clause_index);
  lc_map_t *m;
  int lit;

  for (; clause_ptr < end_ptr; clause_ptr++) {
    lit = *clause_ptr;
    m = &l->lits_clauses[lit];
    srid_t size = m->size;

    // Allocate more memory, if needed
    if (size >= m->alloc_size) {
      lc_map_realloc(m);
    }
     
    // NOTE: Realloc must come before this variable, or else pointer is stale
    srid_t *clauses = m->clauses;

    // Store the new clause at the end if it is larger than all stored clauses
    if (size == 0 || clause_index > clauses[size - 1]) {
      clauses[m->size] = clause_index;
      // Edge case: we are adding a clause after deleting all smaller ones.
      // If this is truly the first clause, `size == 0`.
      if (l->lits_occurrences[lit] == 1) {
        m->start_idx = size;
      }
      m->size++;
      m->end_idx = m->size; // Exclusive index
    } else if (l->lits_occurrences[lit] == 1) {
      // Edge case: we are restoring a clause after deleting all others.
      // Scan the clauses for this one, and set start and end accordingly.
      int found_match = 0;
      for (srid_t i = 0; i < size; i++) {
        if (clauses[i] == clause_index) {
          m->start_idx = i;
          m->end_idx = i + 1;
          found_match = 1;
          break;
        }
      }

      if (!found_match) {
        goto err_could_not_find_mapping;
      }
    } else {
      // The clause lies within the ones we've already stored.
      // Update the start/end indexes, if necessary.
      srid_t first_active_clause = clauses[m->start_idx];
      srid_t last_active_clause = clauses[m->end_idx - 1];

      if (clause_index > last_active_clause) {
        // Scan forwards
        srid_t size = m->size;
        int updated_end = 0;
        for (srid_t i = m->end_idx; i < size; i++) {
          if (clauses[i] == clause_index) {
            m->end_idx = i + 1; // Exclusive index
            updated_end = 1;
            break;
          }
        }

        if (!updated_end) {
          goto err_could_not_find_mapping;
        }
      } else if (clause_index < first_active_clause) {
        // Scan backwards
        int updated_start = 0;
        for (srid_t i = m->start_idx - 1; i >= 0; i--) {
          if (clauses[i] == clause_index) {
            m->start_idx = i;
            updated_start = 1;
            break;
          }
        }

        if (!updated_start) {
          goto err_could_not_find_mapping;
        }
      }
    }
  }

  return; // Only go to the error case via `goto`
  err_could_not_find_mapping:
  logc("%d %d %d %d", m->start_idx, m->end_idx, m->size, m->alloc_size);
  dbg_print_lit_occ_for_lit(l, lit);
  log_fatal_err("Could not find clause %lld in mapping for lit %d.",
      TO_DIMACS_CLAUSE(clause_index), TO_DIMACS_LIT(lit));
}

static void store_formula_clause_mappings(lit_occ_t *l, srid_t until_clause) {
  // Allocate the literal-to-clauses arrays for each literal.
  for (int lit = 0; lit < l->alloc_size; lit++) {
    srid_t occs = l->lits_occurrences[lit];
    if (occs == 0) continue;

    srid_t alloc_size = MAX(occs, MIN_LITS_CLAUSES_INNER_ARRAY_SIZE);
    lc_map_t *m = &l->lits_clauses[lit];
    m->clauses = xmalloc(alloc_size * sizeof(srid_t));
    m->alloc_size = alloc_size;
  }

  // Now store the clause mappings for the formula
  for (srid_t c = 0; c < until_clause; c++) {
    store_clause_mapping(l, c);
  }
}

void lit_occ_add_formula_until(lit_occ_t *l, srid_t max_clause_index) {
  lit_occ_realloc_no_clause_mappings(l);
  store_formula_occurrences(l, max_clause_index);
}

void lit_occ_add_formula_until_with_clause_mappings(
    lit_occ_t *l, srid_t max_clause_index) {
  lit_occ_realloc_with_clause_mappings(l);
  store_formula_occurrences(l, max_clause_index);
  store_formula_clause_mappings(l, max_clause_index);
}

void lit_occ_add_formula(lit_occ_t *l) {
  lit_occ_add_formula_until(l, formula_size);
}

void lit_occ_add_formula_with_clause_mappings(lit_occ_t *l) {
  lit_occ_add_formula_until_with_clause_mappings(l, formula_size);
}

// Adds occurrences for this clause.
// Assumes that clauses are added in increasing order.
// This function has no effect if the clause is deleted.
void lit_occ_add_clause(lit_occ_t *l, srid_t clause_index) {
  if (is_clause_deleted(clause_index)) return;

  if (MAX_LIT > l->alloc_size) {
    lit_occ_realloc(l);
  }

  store_clause_occurrences(l, clause_index);
  if (l->lits_clauses != NULL) {
    store_clause_mapping(l, clause_index);
  }
}

srid_t get_lit_occurrences(lit_occ_t *l, int lit) {
  if (lit >= l->alloc_size) {
    return 0;
  } else {
    return l->lits_occurrences[lit];
  }
}

static inline fl_clause_t *get_first_last_clause_for_lit_unsafe(lit_occ_t *l, int lit) {
  return &l->lits_first_last_clauses[lit];
}

/**
 * @brief Returns a pointer to the `fl_clause_t` struct for the given literal.
 * 
 * If `lit` is out of bounds, returns `NULL`.
 * 
 * Note: the pointer is only valid until a new clause is added or deleted.
 */
fl_clause_t *get_first_last_clause_for_lit(lit_occ_t *l, int lit) {
  if (lit >= l->alloc_size) {
    return NULL;
  } else {
    return get_first_last_clause_for_lit_unsafe(l, lit);
  }
}

/**
 * @brief Get the first and last clause for the provided `clause`.
 *        Stores the result in the provided `fl_clause_t` struct.
 * 
 * @param[out] fl The location to write the first/last clause information.
 */
void get_first_last_clause_for_clause(lit_occ_t *l, srid_t clause, fl_clause_t *fl) {
  if (is_clause_deleted(clause)) {
    fl->first_clause = 0;
    fl->last_clause = -1;
    return;
  }

  srid_t min = formula_size + 1;
  srid_t max = -1;
  int *clause_ptr = get_clause_start_unsafe(clause);
  int *end_ptr = get_clause_end(clause);

  for (; clause_ptr < end_ptr; clause_ptr++) {
    int lit = *clause_ptr;
    fl_clause_t *lit_fl = get_first_last_clause_for_lit(l, lit);

    // Assumes that the pointer is not NULL
    // Assumes that the first/last structure has been maintained correctly
    // (In other words, since `lit` appears in the formula, it is in `l`.)
    SET_MIN_LEFT(min, lit_fl->first_clause);
    SET_MAX_LEFT(max, lit_fl->last_clause);
  }

  fl->first_clause = min;
  fl->last_clause = max;
}

static void move_first_forward(lit_occ_t *l, int lit, fl_clause_t *fl) {
  if (l->lits_clauses != NULL) {
    // Scan forwards until we find a non-deleted clause
    int end_idx = END_IDX_INCLUSIVE(l, lit);
    srid_t *clauses = &CLAUSE_AT_START_IDX(l, lit);
    for (int idx = START_IDX(l, lit) + 1; idx < end_idx; idx++) {
      clauses++;
      srid_t c = *clauses; 
      if (!is_clause_deleted(c)) {
        START_IDX(l, lit) = idx;
        fl->first_clause = c;
        return;
      }
    }

    START_IDX(l, lit) = end_idx;
    fl->first_clause = CLAUSE_AT_END_IDX(l, lit);
  } else {
    // We scan forwards until we find a clause with this literal
    srid_t last = fl->last_clause;
    for (srid_t c = fl->first_clause + 1; c < last; c++) {
      if (is_clause_deleted(c)) continue;

      int *clause_ptr = get_clause_start_unsafe(c);
      int *end_ptr = get_clause_end(c);
      for (; clause_ptr < end_ptr; clause_ptr++) {
        if (*clause_ptr == lit) {
          fl->first_clause = c;
          return;
        }
      }
    }
    
    fl->first_clause = last;
  }
}

static void move_last_backward(lit_occ_t *l, int lit, fl_clause_t *fl) {
  if (l->lits_clauses != NULL) {
    // Scan backwards until we find a non-deleted clause
    int start_idx = START_IDX(l, lit) + 1;
    srid_t *clauses = &CLAUSE_AT_END_IDX(l, lit);
    for (int idx = END_IDX(l, lit) - 1; idx > start_idx; idx--) {
      // idx is exclusive in this loop...
      clauses--;
      srid_t c = *clauses; 
      if (!is_clause_deleted(c)) {
        END_IDX(l, lit) = idx; // ...so that way, it's exclusive here
        fl->last_clause = c;
        return;
      }
    }

    END_IDX(l, lit) = start_idx;
    fl->last_clause = CLAUSE_AT_START_IDX(l, lit);
  } else {
    // We scan backwards until we find a clause with this literal
    srid_t first = fl->first_clause;
    for (srid_t c = fl->last_clause - 1; c > first; c--) {
      if (is_clause_deleted(c)) continue;

      int *clause_ptr = get_clause_start_unsafe(c);
      int *end_ptr = get_clause_end(c);
      for (; clause_ptr < end_ptr; clause_ptr++) {
        if (*clause_ptr == lit) {
          fl->last_clause = c;
          return;
        }
      }
    }

    fl->last_clause = first;
  }
}

/**
 * @brief Deletes the effect of the clause on the `lit_occ_t` structure.
 * 
 * This function must be called before the clause is actually deleted from
 * the CNF formula, so as to allow the function to loop over the literals.
 * 
 * Also updates the first/last clause information for each literal
 * in the clause. If `lits_clauses` are active, then the first and last
 * indexes might get updated, but the contents of the `lits_clauses` arrays
 * are not changed.
 */
void lit_occ_delete_clause(lit_occ_t *l, srid_t clause_index) {
  FATAL_ERR_IF(is_clause_deleted(clause_index),
    "lit_occ_delete_clause(): Clause %lld was already deleted.",
    TO_DIMACS_CLAUSE(clause_index));

  int *clause_ptr = get_clause_start_unsafe(clause_index);
  int *end_ptr = get_clause_end(clause_index);
  for (; clause_ptr < end_ptr; clause_ptr++) {
    int lit = *clause_ptr;
    fl_clause_t *fl = get_first_last_clause_for_lit_unsafe(l, lit);
    
    int occs = --l->lits_occurrences[lit];
    if (occs == 0) {
      memset(fl, 0xff, sizeof(fl_clause_t));
      if (l->lits_clauses != NULL) {
        lc_map_t *m = &l->lits_clauses[lit];
        m->start_idx = 0;
        m->end_idx = 0;
      }
    } else if (occs > 0) {
      if (fl->first_clause == clause_index) {
        move_first_forward(l, lit, fl);
      }

      // After moving forward, we might have a single occurrence left.
      // Don't move the last clause backwards if we just moved it forwards
      if (fl->first_clause == fl->last_clause) {
        continue;
      }

      // Otherwise, we might have to move the last clause backwards
      if (fl->last_clause == clause_index) {
        move_last_backward(l, lit, fl);
      }
    } else {
      log_fatal_err("lit_occ_delete_clause(): Literal %d has negative "
        "occurrences (%d) after deleting clause %lld.",
        TO_DIMACS_LIT(lit), occs, TO_DIMACS_CLAUSE(clause_index));
    }
  }
}

// Returns the pointer to the first clause containing `lit`.
// Pointer guaranteed to lie on a contiguous block of clauses containing lit.
srid_t *get_first_clause_containing_lit(lit_occ_t *l, int lit) {
  if (lit >= l->alloc_size || l->lits_clauses == NULL) {
    return NULL;
  } else {
    return &CLAUSE_AT_START_IDX(l, lit);
  }
}

// Returns the (inclusive) pointer to the last clause containing `lit`.
srid_t *get_last_clause_containing_lit(lit_occ_t *l, int lit) {
  if (lit >= l->alloc_size || l->lits_clauses == NULL) {
    return NULL;
  } else {
    return &CLAUSE_AT_END_IDX(l, lit);
  }
}

void dbg_print_lit_occ_for_lit(lit_occ_t *l, int lit) {
  if (lit < 0 || lit >= l->alloc_size) {
    logc("Literal %d out of bounds (max %d)",
        TO_DIMACS_LIT(lit), l->alloc_size - 1);
    return;
  }

  int occ = l->lits_occurrences[lit];
  srid_t first, last;
  fl_clause_t *fl = &l->lits_first_last_clauses[lit];
  if (occ > 0) {
    first = fl->first_clause;
    last = fl->last_clause;
  } else {
    first = -1;
    last = -1;
  }

  logc_raw("[Lit %d] #occs = %d, first = %lld, last = %lld",
        TO_DIMACS_LIT(lit), occ,
        TO_DIMACS_CLAUSE(first), TO_DIMACS_CLAUSE(last));
  if (l->lits_clauses != NULL) {
    logc_raw(", st_id = %lld, end_id = %lld, size = %lld, alloc_size = %lld, clauses:",
      START_IDX(l, lit), END_IDX(l, lit),
      SIZE_IDX(l, lit), l->lits_clauses[lit].alloc_size);
    srid_t *clauses = CLAUSES(l, lit);

    for (int i = 0; i < START_IDX(l, lit); i++) {
      srid_t clause_idx = clauses[i];
      logc_raw(" (%lld)", TO_DIMACS_CLAUSE(clause_idx));
    }

    for (int i = START_IDX(l, lit); i < END_IDX(l, lit); i++) {
      srid_t clause_idx = clauses[i];
      logc_raw(" %lld", TO_DIMACS_CLAUSE(clause_idx));
    }

    for (int i = END_IDX(l, lit); i < SIZE_IDX(l, lit); i++) {
      srid_t clause_idx = clauses[i];
      logc_raw(" (%lld)", TO_DIMACS_CLAUSE(clause_idx));
    }
  }
  logc_raw("\n"); 
}

void dbg_print_lit_occ(lit_occ_t *l) {
  for (int lit = 0; lit < l->alloc_size; lit++) {
    dbg_print_lit_occ_for_lit(l, lit);
  }
}

/**
 * @brief Validates the internal consistency of the `lit_occ_t` struct.
 * 
 * Used for comparing the occurrences counts with the literal-clause
 * mappings. For example, if the occurrences claims that literal 5 has
 * three occurrences, then `lits_clauses[lit]` should be tracking
 * (at least) three clauses that are not deleted in the formula.
 * 
 * Throws an error and prints debug information on the first inconsistency.
 */
void lit_occ_validate(lit_occ_t *l) {
  if (l->lits_clauses == NULL) {
    return;
  }

  // Loop through all literals, and check that all active clauses
  // add up to expected number of occurrences
  int alloc_size = l->alloc_size;
  for (int lit = 0; lit < alloc_size; lit++) {
    srid_t occs = l->lits_occurrences[lit];
    lc_map_t *m = &l->lits_clauses[lit];
    if (m->clauses == NULL) {
      if (occs > 0) {
        log_fatal_err("Literal %d has %lld occurrences but no clause mapping.",
            TO_DIMACS_LIT(lit), occs);
      } else {
        continue;
      }
    }

    srid_t *clauses = &CLAUSE_AT_START_IDX(l, lit);
    srid_t *end = &CLAUSE_AT_END_IDX(l, lit);
    srid_t *size_end = &CLAUSE_AT_SIZE_IDX(l, lit);
    for (; clauses <= end; clauses++) {
      if (!is_clause_deleted(*clauses)) {
        occs--;
      }
    }

    if (occs != 0) {
      logc("Occurrences didn't match for literal %d: expected %lld, found %lld",
          TO_DIMACS_LIT(lit), l->lits_occurrences[lit],
          l->lits_occurrences[lit] - occs);
      dbg_print_lit_occ_for_lit(l, lit);
      log_fatal_err("Literal %d occurrence count mismatch after validation.",
          TO_DIMACS_LIT(lit));
    }
  }
}