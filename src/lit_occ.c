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

#define CLAUSES(l, lit)             (l->lits_clauses[lit].clauses)
#define CLAUSE_AT_START_IDX(l, lit) (CLAUSES(l, lit)[START_IDX(l, lit)])
#define CLAUSE_AT_END_IDX(l, lit)   (CLAUSES(l, lit)[END_IDX_INCLUSIVE(l, lit)])

#ifndef FREE_IF_NOT_NULL
#define FREE_IF_NOT_NULL(ptr)   \
  if ((ptr) != NULL) {                    \
    xfree(ptr);                           \
  }
#endif

static inline void lc_map_init(lc_map_t *m) {
  memset(m, 0, sizeof(lc_map_t));
}

static inline void lc_map_destroy(lc_map_t *m) {
  if (m->clauses != NULL) {
    xfree(m->clauses);
  }

  memset(m, 0, sizeof(lc_map_t));
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
static void lit_occ_realloc(lit_occ_t *l, int with_lits_clauses) {
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
  lit_occ_realloc(l, 0);
}

static void lit_occ_realloc_with_clause_mappings(lit_occ_t *l) {
  lit_occ_realloc(l, 1);
}

static void store_clause_occurrences(lit_occ_t *l, srid_t clause_index) {
  if (is_clause_deleted(clause_index)) return;
  int *clause_ptr = get_clause_start_unsafe(clause_index);
  int *end_ptr = get_clause_end(clause_index);
  for (; clause_ptr < end_ptr; clause_ptr++) {
    int lit = *clause_ptr;
    l->lits_occurrences[lit]++;

    // Always update the last clause, but update the first clause only once
    l->lits_first_last_clauses[lit].last_clause = clause_index;
    if (l->lits_occurrences[lit] == 1) {
      l->lits_first_last_clauses[lit].first_clause = clause_index;
    }
  }
}

// Stores occurrences and f/l clauses in `l` by looping across the formula.
// Assumes that the `alloc()` functions have already been called.
// Assumes that `max_var` hasn't grown in the intervening time.
static void store_formula_occurrences(lit_occ_t *l, srid_t until_clause) {
  for (srid_t c = 0; c < until_clause; c++) {
    store_clause_occurrences(l, c);
  }
}

static void store_clause_mapping(lit_occ_t *l, srid_t clause_index) {
  if (is_clause_deleted(clause_index)) return;
  int *clause_ptr = get_clause_start_unsafe(clause_index);
  int *end_ptr = get_clause_end(clause_index);
  for (; clause_ptr < end_ptr; clause_ptr++) {
    int lit = *clause_ptr;

    // Resize if necessary
    srid_t current_size = l->lits_clauses[lit].end_idx;
    srid_t alloc_size = l->lits_clauses[lit].alloc_size;
    if (current_size >= alloc_size) {
      alloc_size = RESIZE(alloc_size);
      l->lits_clauses[lit].clauses = xrealloc(l->lits_clauses[lit].clauses,
          alloc_size * sizeof(srid_t));
      l->lits_clauses[lit].alloc_size = alloc_size;
    }

    l->lits_clauses[lit].clauses[current_size] = clause_index;
    l->lits_clauses[lit].end_idx++;
  }
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
// Assumes the new clause hasn't had its occurrences added yet.
// In other words, assumes the clause is a new proof line.
void lit_occ_add_clause(lit_occ_t *l, srid_t clause_index) {
  if (MAX_LIT > l->alloc_size) {
    if (l->lits_clauses == NULL) {
      lit_occ_realloc_no_clause_mappings(l);
    } else {
      lit_occ_realloc_with_clause_mappings(l);
    }
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
    min = MIN(min, lit_fl->first_clause);
    max = MAX(max, lit_fl->last_clause);
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
    // We scan the formula until we find a clause with this literal
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
    // We scan the formula backwards until we find a clause with this literal
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

// Must be called before formula deletion, so the clause can be looped over.
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
      // Clear the f/l and clauses structures
      memset(fl, 0xff, sizeof(fl_clause_t));
      if (l->lits_clauses != NULL) {
        // TODO: adversarial case of removing and adding the same literal?
        lc_map_destroy(&l->lits_clauses[lit]);
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

void dbg_print_lit_occ_for_lit(lit_occ_t *l, int lit) {
  if (lit < 0 || lit >= l->alloc_size) {
    logc("Literal %d out of bounds (max %d)", TO_DIMACS_LIT(lit), l->alloc_size - 1);
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
  if (l->lits_clauses != NULL && l->lits_occurrences[lit] > 2) {
    logc_raw(", clauses:");
    srid_t *clauses = CLAUSES(l, lit);
    for (int i = START_IDX(l, lit); i < END_IDX(l, lit); i++) {
      srid_t clause_idx = clauses[i];
      logc_raw(" %lld", TO_DIMACS_CLAUSE(clause_idx));
    }
  }
  logc_raw("\n"); 
}

void dbg_print_lit_occ(lit_occ_t *l) {
  for (int lit = 0; lit < l->alloc_size; lit++) {
    dbg_print_lit_occ_for_lit(l, lit);
  }
}