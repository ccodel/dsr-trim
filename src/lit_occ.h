/**
 * @file lit_occ.h
 * @brief Tracks the number of times and the clauses that literals occur in.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-12-11
 */

#ifndef _LIT_OCC_H_
#define _LIT_OCC_H_

#include "global_types.h"

/**
 * @brief Stores the first and last clause IDs for a particular literal.
 * 
 * These are used to calculate the set of clauses that need to be checked
 * for witness reduction during DSR/LSR checking. Clauses outside this
 * range can be skipped, since the witness does not affect them.
 */
typedef struct first_last_clause_for_lit {
  srid_t first_clause;
  srid_t last_clause;
} fl_clause_t;

typedef struct lit_clause_mapping {
  srid_t *clauses;
  srid_t start_idx;   // Inclusive index into `clauses`. Often 0
  srid_t end_idx;     // Exclusive index into `clauses`. The "size".
  srid_t alloc_size;  // The allocated size of `clauses`.
  // NOTE: when `srid_t` is an int, this wastes space due to struct padding.
} lc_map_t;

/**
 * @brief This structure tracks how often and in which clauses literals occur.
 * 
 * `lits_occurrences` counts the number of times each literal
 * appears in the formula.
 * 
 * `lits_f_l_clauses` stores the first and last clause IDs for each literal.
 * Must be updated when clauses get added and deleted.
 * 
 * `lits_clauses` is an array to `lc_map_t` structs, containing literal-clause
 * mappings. Indexes into this list are maintained to speed up the updating
 * of `lits_first_last_clauses` on clause deletion.
 * 
 * `alloc_size` stores the number of literals this struct is tracking.
 * Acts as the "allocated size" of the various arrays.
 */
typedef struct lit_occurrence_data {
  srid_t *lits_occurrences;
  fl_clause_t *lits_first_last_clauses;
  lc_map_t *lits_clauses;
  int alloc_size;
} lit_occ_t;

void lit_occ_init(lit_occ_t *l);
void lit_occ_destroy(lit_occ_t *l);

void lit_occ_add_formula(lit_occ_t *l);
void lit_occ_add_formula_with_clause_mappings(lit_occ_t *l);
void lit_occ_add_formula_until(lit_occ_t *l, srid_t max_clause_index);
void lit_occ_add_formula_until_with_clause_mappings(
  lit_occ_t *l, srid_t max_clause_index);

void lit_occ_add_clause(lit_occ_t *l, srid_t clause_index);
void lit_occ_delete_clause(lit_occ_t *l, srid_t clause_index);

srid_t get_lit_occurrences(lit_occ_t *l, int lit);
fl_clause_t *get_first_last_clause_for_lit(lit_occ_t *l, int lit);
void get_first_last_clause_for_clause(lit_occ_t *l, srid_t clause, fl_clause_t *fl);

void dbg_print_lit_occ_for_lit(lit_occ_t *l, int lit);
void dbg_print_lit_occ(lit_occ_t *l);

#endif /* _LIT_OCC_H_ */