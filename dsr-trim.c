/**
 * @file sr-trim.c
 * @brief Tool for labeling and trimming SR proof certificates.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-12
 */

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>

#include "xio.h"
#include "global_data.h"
#include "cnf_parser.h"
#include "sr_parser.h"
#include "xmalloc.h"

/*
TODOs:
  - Witness minimization. Will probably have to write a new assume_subst()
    function that does this.
  - Candidate clause minimization. When marking clauses, mark literals as well.
  - To handle future clause deletion, use the "safe" version of get_clause().
  - Watch pointer de-sizing.
*/

////////////////////////////////////////////////////////////////////////////////

#define INIT_LIT_WP_ARRAY_SIZE    (4)

// When setting literals "globally" under initial unit propagation, we use the
// largest possible generation value. We use longs, so we use LONG_MAX.
#define GLOBAL_GEN                (LONG_MAX)
#define ASSUMED_GEN               (LONG_MAX - 1)

// SR trim as a state machine, for different parts of UP.
typedef enum sr_trim_state {
  GLOBAL_UP,
  CANDIDATE_UP,
  RAT_UP,
} state_t;

static state_t state;

// TODO: dpr-trim has watch pointers, clause ids, etc. as longs and not ints.
// Possible reason is the additional two bits of info in the least-siginificant bits
// For now, we'll keep them as ints and revisit this later.

// 2D array of watch pointers, indexed by literals. Initialized to NULL for each literal.
static int **wps = NULL;

// Allocated size of the 2D array of watch pointers.
static int wps_alloc_size = 0;

// Allocated size of watch pointer array for each literal.
// Invariant: if wps[i] == NULL, then wp_alloc_sizes[i] = 0.
static int *wp_alloc_sizes = NULL;

// Number of watch pointers under each literal.
// Invariant: if wps[i] == NULL, then wp_sizes[i] = 0.
static int *wp_sizes = NULL; // TODO: New name

// Array containing the clause ID "reason" causing the variable to be set. Indexed by variable.
static int *up_reasons = NULL;
static int up_reasons_alloc_size = 0; // TODO: use alpha_subst_alloc_size for this?

// A list of literals, in order of when they become unit
static int *unit_literals = NULL;
static int *unit_clauses = NULL;
static int units_alloc_size = 0;
static int unit_literals_size = 0;
static int unit_clauses_size = 0;

static int candidate_unit_clauses_index = 0;
static int RAT_unit_clauses_index = 0;

// Index pointing at the "unprocessed" global UP literals
static int global_up_literals_index = 0;

// Monotonically increased index into the formula
static int wp_processed_clauses = 0;

static int candidate_assumed_literals_index = 0;
static int candidate_unit_literals_index = 0;
static int RAT_assumed_literals_index = 0;
static int RAT_unit_literals_index = 0;

// Generation bumping for indicating that clauses are involved in UP derivations. Indexed by clauses.
static long *dependency_markings = NULL;
static int dependencies_alloc_size = 0;

// When assuming the RAT clause under the substitution, we record specially
// marked variables here for tautology checking. Cleared when a trivial
// UP derivation is not found, or if one is found not based on a RAT-marked var.
static int *RAT_marked_vars = NULL;
static int RAT_marked_vars_alloc_size = 0;
static int RAT_marked_vars_size = 0;

static int derived_empty_clause = 0;

// We store the RAT derivations as they come in "printable" format.
static int *lsr_line = NULL;
static int lsr_line_alloc_size = 0;
static int lsr_line_size = 0;

static FILE *sr_certificate_file = NULL;
static long current_line = 0; // For printing the correct line ID
static long generation_before_line_checking = 0;
static int up_falsified_clause = -1; // Set by unit propagation, -1 if none found

static FILE *lsr_proof_file = NULL;

////////////////////////////////////////////////////////////////////////////////

static void print_usage(void) {
  printf("c Usage: ./sr-trim <cnf-file> <pf-file> [lsr-file]\n");
}

static void init_sr_trim_data(void) {
  // Allocate an empty watch pointer array for each literal
  // Allocate some additional space, since we'll probably add new literals later
  wps_alloc_size = max_var * 4;
  wps = xcalloc(wps_alloc_size, sizeof(int *));
  wp_alloc_sizes = xcalloc(wps_alloc_size, sizeof(int)); 
  wp_sizes = xcalloc(wps_alloc_size, sizeof(int));

  // Only allocate initial watch pointer space for literals that appear in the formula 
  for (int i = 0; i < max_var * 2; i++) {
    wp_alloc_sizes[i] = INIT_LIT_WP_ARRAY_SIZE;
    wps[i] = xmalloc(INIT_LIT_WP_ARRAY_SIZE * sizeof(int));
  }

  // Allocate empty reasons array for each variable, plus extra space
  up_reasons_alloc_size = max_var * 2;
  up_reasons = xmalloc(up_reasons_alloc_size * sizeof(int));
  memset(up_reasons, 0xff, up_reasons_alloc_size * sizeof(int)); // Set to -1

  // Allocate space for the unit lists. Probably won't be too large
  units_alloc_size = max_var * 2;
  unit_literals = xmalloc(units_alloc_size * sizeof(int));
  unit_clauses = xmalloc(units_alloc_size * sizeof(int));

  // Allocate space for the dependency markings
  dependencies_alloc_size = formula_size * 2;
  dependency_markings = xcalloc(dependencies_alloc_size, sizeof(long));

  RAT_marked_vars_alloc_size = max_var;
  RAT_marked_vars = xmalloc(RAT_marked_vars_alloc_size * sizeof(int));

  // Allocate space for the printable LSR line, for RAT derivations.
  lsr_line_alloc_size = formula_size;
  lsr_line = xmalloc(lsr_line_alloc_size * sizeof(int));

  current_line = formula_size;
}

static void resize_sr_trim_data(void) {
  // Resize arrays that depend on max_var and formula_size
  // The memset() calls don't do anything in the case of no allocation
  int old_size = up_reasons_alloc_size;
  RESIZE_ARR(up_reasons, up_reasons_alloc_size, max_var, sizeof(int));
  memset(up_reasons + old_size, 0xff, (up_reasons_alloc_size - old_size) * sizeof(int));

  old_size = wps_alloc_size;
  RESIZE_ARR(wps, wps_alloc_size, max_var * 2, sizeof(int *));
  memset(wps + old_size, 0, (wps_alloc_size - old_size) * sizeof(int *));

  old_size = dependencies_alloc_size;
  RESIZE_ARR(dependency_markings, dependencies_alloc_size, formula_size, sizeof(long));
  memset(dependency_markings + old_size, 0, (dependencies_alloc_size - old_size) * sizeof(long));
}

static inline void resize_units(void) {
  if (unit_literals_size >= units_alloc_size) {
    units_alloc_size = RESIZE(unit_literals_size);
    unit_literals = xrealloc(unit_literals, units_alloc_size * sizeof(int));
    unit_clauses = xrealloc(unit_clauses , units_alloc_size * sizeof(int));
  }
}

////////////////////////////////////////////////////////////////////////////////

// Prints the new clause to the LSR file.
// Doesn't print anything if the empty clause has been derived.
static void print_clause(void) {
  if (!derived_empty_clause) {
    for (int i = formula[formula_size]; i < lits_db_size; i++) {
      fprintf(lsr_proof_file, "%d ", TO_DIMACS_LIT(lits_db[i]));
    }
  }
}

static void print_witness(void) {
  for (int i = 0; i < witness_size; i++) {
    // Add the pivot as a separator, if there's a substitution part of the witness
    if (i == subst_index) {
      fprintf(lsr_proof_file, "%d ", TO_DIMACS_LIT(pivot));
    }
    fprintf(lsr_proof_file, "%d ", TO_DIMACS_LIT(witness[i]));
  }
}

static inline void print_active_dependencies(void) {
  for (int i = 0; i < unit_clauses_size; i++) {
    if (dependency_markings[unit_clauses[i]] > generation_before_line_checking) {
      fprintf(lsr_proof_file, "%d ", unit_clauses[i] + 1); // Add 1 for DIMACS
    }
  }
}

// Prints the accumulated LSR line, after computing dependencies.
// Should be printed before incrementing the generation.
// The kind of line printed depends on the global state_t.
static void print_lsr_line(void) {
  FILE *f = lsr_proof_file;
  current_line++;
  fprintf(f, "%ld ", current_line);

  // Prints the clause to be added, or nothing if we derived the empty clause
  print_clause();

  // If there are no stored RAT derivations, then no need to print a witness
  if (lsr_line_size > 0) {
    print_witness();
  }

  fprintf(f, "0 ");
  print_active_dependencies();

  // If there are no RAT derivations, print the falsifying clause
  if (lsr_line_size == 0 && up_falsified_clause != -1) {
    fprintf(f, "%d ", up_falsified_clause + 1); // Add 1 to print it in DIMACS
  } else {
    // Print the RAT derivations
    // In rare cases, up_falsified_clause == -1, meaning that we *did* do RAT
    // checking, but there were no RAT clauses, in which case this portion will be empty
    for (int i = 0; i < lsr_line_size; i++) {
      fprintf(f, "%d ", lsr_line[i]);
    }
  }

  fprintf(f, "0\n");
}

static inline void clear_lsr_line(void) {
  lsr_line_size = 0;
}

static inline void add_RAT_clause_to_lsr_line(int clause) {
  RESIZE_ARR(lsr_line, lsr_line_alloc_size, lsr_line_size, sizeof(int));
  lsr_line[lsr_line_size++] = -(clause + 1);
}

static inline void add_clause_to_lsr_line(int clause) {
  RESIZE_ARR(lsr_line, lsr_line_alloc_size, lsr_line_size, sizeof(int));
  lsr_line[lsr_line_size++] = (clause + 1);
}

// Marks the clauses causing each literal in the clause to be false.
// Ignore literals that are assumed fresh, whether in CANDIDATE or RAT.
// Literals that were globally set to unit, but are candidate assumed, are ignored.
static inline void mark_clause(int clause, int offset) {
  int *clause_ptr = get_clause_start_unsafe(clause) + offset; 
  int *clause_end = get_clause_start_unsafe(clause + 1);
  for (; clause_ptr < clause_end; clause_ptr++) {
    int lit = *clause_ptr;
    int var = VAR_FROM_LIT(lit);
    int reason = up_reasons[var];
    if (reason >= 0) {
      dependency_markings[reason] = alpha_generation;
    }
  }
}

static inline void mark_unit_clause(int clause) {
  mark_clause(clause, 1);
}

static inline void mark_entire_clause(int clause) {
  mark_clause(clause, 0);
}

// Start marking backwards, assuming the offending clause has already been marked.
static inline void mark_dependencies(void) {
  for (int i = unit_clauses_size - 1; i >= 0; i--) {
    int clause = unit_clauses[i];
    if (dependency_markings[clause] == alpha_generation) {
      mark_unit_clause(clause);
    }
  }
}

// Backwards marks the dependencies for the UP derivation.
// Starts the marking at the clause stored in up_falsified_clause.
// NOTE: Every marked clause is stored in unit_clauses, except for up_falsified_clause,
// which is not marked.
static inline void mark_up_derivation(void) {
  mark_entire_clause(up_falsified_clause);
  mark_dependencies();
}

static void store_RAT_dependencies() {
  for (int i = RAT_unit_clauses_index; i < unit_clauses_size; i++) {
    if (dependency_markings[unit_clauses[i]] == alpha_generation) {
      add_clause_to_lsr_line(unit_clauses[i]);
    }
  }

  add_clause_to_lsr_line(up_falsified_clause);
}

// Moves state from GLOBAL_UP -> CANDIDATE_UP -> RAT_UP.
// Sets the various indexes appropriately.
// If incremented at RAT_UP, resets "back to" a RAT_UP state.
static void increment_state(void) {
  switch (state) {
    case GLOBAL_UP:
      state = CANDIDATE_UP;
      candidate_assumed_literals_index = unit_literals_size;
      candidate_unit_literals_index = unit_literals_size;
      candidate_unit_clauses_index = unit_clauses_size;
      break;
    case CANDIDATE_UP:
      state = RAT_UP;
      RAT_assumed_literals_index = unit_literals_size;
      RAT_unit_literals_index = unit_literals_size;
      RAT_unit_clauses_index = unit_clauses_size;
      break;
    case RAT_UP:
      unit_literals_size = RAT_assumed_literals_index;
      RAT_unit_literals_index = RAT_assumed_literals_index;
      unit_clauses_size = RAT_unit_clauses_index;
      break;
    default: PRINT_ERR_AND_EXIT("Corrupted state.");
  }
}

// Moves state from RAT_UP -> CANDIDATE_UP -> GLOBAL_UP.
// Sets the various indexes appropriately.
static void decrement_state(void) {
  switch (state) {
    case GLOBAL_UP: return;
    case CANDIDATE_UP:
      state = GLOBAL_UP;
      unit_literals_size = candidate_assumed_literals_index;
      unit_clauses_size = candidate_unit_clauses_index;
      break;
    case RAT_UP:
      state = CANDIDATE_UP;
      unit_literals_size = RAT_assumed_literals_index;
      unit_clauses_size = RAT_unit_clauses_index;
      break;
    default: PRINT_ERR_AND_EXIT("Corrupted state.");
  }
}

// Sets the literal to true, and adds it to the unit_literals array.
// Infers the correct generation value from state.
static inline void assume_unit_literal(int lit) {
  long gen = (state == CANDIDATE_UP) ? ASSUMED_GEN : alpha_generation;
  set_lit_for_alpha(lit, gen);
  resize_units();
  unit_literals[unit_literals_size++] = lit;

  // TODO: While incrementing is slower than setting it when we're done,
  // there's less chance for bugs. Make it be a setting later.
  if (state == CANDIDATE_UP) {
    candidate_unit_literals_index++;
  } else if (state == RAT_UP) {
    RAT_unit_literals_index++;
  }
}

// Sets the literal in the clause to true, assuming it's unit in the clause.
// Then adds the literal to the unit_literals array, to look for more unit clauses later.
// NOTE: When doing unit propagation, take the negation of the literal in the unit_literals array.
static void set_unit_clause(int lit, int clause, long gen) {
  set_lit_for_alpha(lit, gen);
  up_reasons[VAR_FROM_LIT(lit)] = clause;

  resize_units();
  unit_literals[unit_literals_size++] = lit;
  unit_clauses[unit_clauses_size++] = clause;
}

// Adds a watch pointer for the lit at the specified clause ID
static void add_wp_for_lit(int lit, int clause) {
  // Resize the literal-indexes arrays if lit is outside our allocated bounds
  if (max_var * 2 >= wps_alloc_size) {
    int old_size = wps_alloc_size;
    wps_alloc_size = RESIZE(max_var * 2);
    wps = xrealloc(wps, wps_alloc_size * sizeof(int *));
    wp_alloc_sizes = xrealloc(wp_alloc_sizes, wps_alloc_size * sizeof(int));
    wp_sizes = xrealloc(wp_sizes, wps_alloc_size * sizeof(int));

    // Set to NULL the new spaces in wps
    int added_size = wps_alloc_size - old_size;
    memset(wps + old_size, 0, added_size * sizeof(int *));
    memset(wp_alloc_sizes + old_size, 0, added_size * sizeof(int));
    memset(wp_sizes + old_size, 0, added_size * sizeof(int));
  }

  // Now allocate more space in the wp[lit] array, if needed
  // Handles the case where both are 0 (uninitialized)
  if (wp_sizes[lit] == wp_alloc_sizes[lit]) {
    wp_alloc_sizes[lit] = MAX(INIT_LIT_WP_ARRAY_SIZE, RESIZE(wp_alloc_sizes[lit]));
    wps[lit] = xrealloc(wps[lit], wp_alloc_sizes[lit] * sizeof(int));
  }

  // Finally, add the clause to the wp list
  wps[lit][wp_sizes[lit]] = clause;
  wp_sizes[lit]++;
}

static void remove_wp_for_lit(int lit, int clause) {
  int *wp_list = wps[lit];
  int wp_list_size = wp_sizes[lit];

  // Find the clause in the wp list and remove it
  for (int i = 0; i < wp_list_size; i++) {
    if (wp_list[i] == clause) {
      // Overwrite the removed clause with the last clause in the list
      wp_list[i] = wp_list[wp_list_size - 1];
      wp_sizes[lit]--;
      return;
    }
  }

  // TODO: If below some threshold of size/alloc_sizes, shrink the array
}

// Performs unit propagation. Sets the falsified clause (the contradiction) to
// up_falsified_clause. -1 if not found.
// Any literals found are set to the provided generation value.
static void perform_up(long gen) {
  /* The unit propagation algorithm is quite involved and immersed in invariants.
   * Buckle up, cowboys.
   *
   * First, we assume that the literals that have been found to be unit have been
   * set to true in the global partial assignment `alpha`. Those literals
   * have been added to the unit_lits array. These are the literals whose 
   * negations can cause additional clauses to become unit.
   * 
   * We take each false literal l and loop through its watch pointers. For any
   * clause with a pair of watch pointers, the watch pointers are two previously-unset 
   * literals (under alpha) in the first two positions of the clause.
   * 
   * We move the other watch pointer p to the first position and check if it is
   * set to true. If so, then we continue to the next clause. Otherwise, we
   * must search through the rest of the clause for a non-false literal. If
   * found, then we swap that literal l' with l, add l' as a watch pointer, and
   * remove l as a watch pointer.
   * 
   * Because l' is not false, then either it is true (in which case, the clause
   * does not become unit), or it is unset. Thus, we might want to check the
   * truth value of p. However, we assumed that p was unset. If, since setting 
   * unit literals, p has become false, then we will detect this in future up_queue
   * literals.
   * 
   * If we can't find a replacement non-false literal l' for l, then we check the
   * truth value of p. If p is false, then we have found a contradiction.
   * Otherwise, we have a new unit, and we continue with unit propagation.
   */

  int i;
  switch (state) {
    case GLOBAL_UP:    i = global_up_literals_index;         break;
    case CANDIDATE_UP: i = candidate_assumed_literals_index; break;
    case RAT_UP:       i = RAT_assumed_literals_index;       break;
    default: PRINT_ERR_AND_EXIT("Corrupted state.");
  }

  // TODO: Better way of doing this, since the size may increase as we do UP?
  up_falsified_clause = -1;
  for (; i < unit_literals_size; i++) {
    int lit = NEGATE_LIT(unit_literals[i]);

    // Iterate through its watch pointers and see if the clause becomes unit
    int *wp_list = wps[lit];
    for (int j = 0; j < wp_sizes[lit]; j++) {
      int clause_id = wp_list[j];
      int *clause = get_clause_start(clause_id);
      const int clause_size = get_clause_size(clause_id);
      
      // Lemma: the clause is not a unit clause (yet), and its watch pointers are 
      // the first two literals in the clause (we may reorder literals here).

      // Place the other watch pointer first
      if (clause[0] == lit) {
        clause[0] = clause[1];
        clause[1] = lit;
      }

      int first_wp = clause[0];

      // If the first watch pointer is true, then the clause is satisfied (not unit)
      if (peval_lit_under_alpha(first_wp) == TT) {
        continue;
      }

      // Otherwise, scan the clause for a non-false literal
      int found_new_wp = 0;
      for (int k = 2; k < clause_size; k++) {
        if (peval_lit_under_alpha(clause[k]) != FF) {
          clause[1] = clause[k];
          clause[k] = lit;
          add_wp_for_lit(clause[1], clause_id);
          // Instead of calling remove_wp_for_lit, we can more intelligently swap
          wp_list[j] = wp_list[wp_sizes[lit] - 1];
          wp_sizes[lit]--;
          found_new_wp = 1;
          break;
        }
      }

      if (found_new_wp) {
        j--;       // We need to decrement, since we replaced wp_list[j]
        continue;  
      }

      // We didn't find a replacement watch pointer. Is the first watch pointer false?
      if (peval_lit_under_alpha(first_wp) == FF) {
        // printf("c       [%ld, UP] Found contradiction in clause %d\n", current_line + 1, clause_id + 1);
        up_falsified_clause = clause_id;
        return;
      } else {
        set_unit_clause(first_wp, clause_id, gen); // Add as a unit literal
      }
    }
  }
  
  if (state == GLOBAL_UP) {
    global_up_literals_index = unit_literals_size;
  }
}

// Adds watch pointers / sets units and performs unit propagation.
// Skips clauses already processed (i.e. when adding a new redundant clause,
// only adds watch pointers/sets unit on that clause).
// Should be called when the global state == GLOBAL_UP.
static void add_wps_and_perform_up() {
  PRINT_ERR_AND_EXIT_IF(state != GLOBAL_UP, "state not GLOBAL_UP.");

  int *clause, *next_clause = get_clause_start_unsafe(wp_processed_clauses);
  int clause_size;

  // Beyond the initial setup, this loop only runs once
  // Make more efficient later?
  for (; wp_processed_clauses < formula_size; wp_processed_clauses++) {
    clause = next_clause;
    next_clause = get_clause_start_unsafe(wp_processed_clauses + 1);
    clause_size = next_clause - clause;

    // If the clause is unit, set it to be true, do UP later. Otherwise, add watch pointers
    if (clause_size == 1) {
      // The clause is unit - examine its only literal
      int lit = *clause;

      // Check if it is falsified - if so, then we have a UP derivation
      if (peval_lit_under_alpha(lit) == FF) {
        derived_empty_clause = 1;
        up_falsified_clause = wp_processed_clauses;
        mark_up_derivation();
        print_lsr_line();
        return;
      } else {
        // Set its one literal globally to true, and add its negation to the UP queue
        // TODO: Possible support for deleting a unit (but Marijn says this won't happen)
        set_unit_clause(lit, wp_processed_clauses, GLOBAL_GEN);
      }
    } else {
      // The clause has at least two literals - make them the watch pointers
      add_wp_for_lit(clause[0], wp_processed_clauses);
      add_wp_for_lit(clause[1], wp_processed_clauses);
    }
  }

  // We don't have an immediate contradiction, so perform unit propagation
  perform_up(GLOBAL_GEN);
  if (up_falsified_clause >= 0) {
    derived_empty_clause = 1;
    mark_up_derivation();
    print_lsr_line();
  }
}

// A clone of of assume_negated_clause() from global_data, but with added bookkeeping. 
// Returns 0 if assumption succeeded, -1 if contradiction found and LSR line emitted.
// Must be called when global state == GLOBAL_UP.
// Even when -1 is returned, the candidate clause is still "assumed".
static int assume_candidate_clause_and_perform_up(void) {
  PRINT_ERR_AND_EXIT_IF(state != GLOBAL_UP, "state not GLOBAL_UP.");
  increment_state();

  // TODO: Find "shortest" UP derivation later
  int satisfied_lit = -1;
  up_falsified_clause = -1; // Clear any previous UP falsifying clause

  for (int i = formula[formula_size]; i < lits_db_size; i++) {
    int lit = lits_db[i];
    int var = VAR_FROM_LIT(lit);

    // Check if the literal is satisfied by prior UP
    // If so, then we have a contradiction
    switch (peval_lit_under_alpha(lit)) {
      case FF:
        // Mark the reason for an already-satisfied literal as assumed
        // This shortens UP derivations
        up_reasons[var] |= MSB32;
        break;
      case UNASSIGNED:
        // Always set (the negations of) unassigned literals to true
        // unassume_candidate_clause() will unassign these
        assume_unit_literal(NEGATE_LIT(lit));
        break;
      case TT:
        // Skip the literal if we already found a satisfying literal
        if (satisfied_lit == -1) {
          satisfied_lit = lit;
          up_falsified_clause = up_reasons[var];
        }
        break;
      default: PRINT_ERR_AND_EXIT("Invalid peval_t value.");
    }
  }

  // If we haven't satisfied the clause, we perform unit propagation
  if (up_falsified_clause == -1) {
    perform_up(ASSUMED_GEN);
  }

  // If we have either satisfied the clause, or found a UP derivation, emit it
  if (up_falsified_clause != -1) {
    mark_up_derivation();
    print_lsr_line();
    return -1;
  }

  return 0;
}

// Reverts changes to the data structures made during the assumption of the candidate clause.
// Must be called before adding the candidate to the formula via insert_clause().
// Decrements global state back to GLOBAL_UP.
static void unassume_candidate_clause(void) {
  PRINT_ERR_AND_EXIT_IF(state != CANDIDATE_UP, "state not CANDIDATE_UP.");

  // Undo the changes we made to the data structures
  // First, address the unit literals set during new UP
  for (int i = candidate_unit_literals_index; i < unit_literals_size; i++) {
    int lit = unit_literals[i];
    int var = VAR_FROM_LIT(lit);

    // Clear the var's reason and generation (since they were derived during candidate UP)
    up_reasons[var] = -1;
    alpha[var] = 0;
  }

  // Now iterate through the clause and undo its changes
  for (int i = formula[formula_size]; i < lits_db_size; i++) {
    int lit = lits_db[i];
    int var = VAR_FROM_LIT(lit);

    if (up_reasons[var] == -1) {
      // If the literal was originally unassigned, set its gen back to 0
      alpha[var] = 0;
    } else if (up_reasons[var] < 0) {
      // The literal was assumed, but not unassigned - undo its assumption bit
      up_reasons[var] ^= MSB32;
    }
  }

  decrement_state();
}

static inline void add_RAT_marked_var(int marked_var) {
  RESIZE_ARR(RAT_marked_vars, RAT_marked_vars_alloc_size, 
    RAT_marked_vars_size, sizeof(int));
  RAT_marked_vars[RAT_marked_vars_size++] = marked_var;
}

static inline void clear_RAT_marked_vars(void) {
  for (int i = 0; i < RAT_marked_vars_size; i++) {
    up_reasons[RAT_marked_vars[i]] ^= MSB32;
  }

  RAT_marked_vars_size = 0;
}

// This is clone of assume_negated_clause_under_subst(), but with extra bookkeeping.
// In particular, we add any set literals to the unit_literals array, for UP purposes.
// Returns the same values as assume_negated_clause_under_subst().
// Sets the indexes values appropriately.
// Call when global state == CANDIDATE_UP.
// Sets the global state to RAT_UP.
static int assume_RAT_clause_under_subst(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(state != CANDIDATE_UP, "state not RAT_UP.");
  increment_state();

  /* If we encounter false literals under alpha, we mark their reasons as assumed
   * in the typical way, but we record which have been marked as assumed only for
   * the RAT clause. This allows us to shorten/detect tautology derivations.
   * However, these markings must be cleared before returning on any code path
   * and before doing normal UP derivation, since we want to record global and
   * candidate UP dependencies accurately.
   * 
   * We might want to do this work in unassume_RAT_clause(), but then UP would
   * have to case on an additional MSB32 bit or pass the dependency index to
   * detect when an assumed variable is a "stopping variable" (global or candidate)
   * or a "non-stopping variable" (RAT). To simplify matters, we clear the
   * RAT_marked_vars array before returning on any code path here. */
  RAT_marked_vars_size = 0;

  int *clause_ptr = get_clause_start(clause_index);
  int *end = get_clause_start(clause_index + 1);
  for (; clause_ptr < end; clause_ptr++) {
    int lit = *clause_ptr;
    int mapped_lit = get_lit_from_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT:
        clear_RAT_marked_vars();
        return SATISFIED_OR_MUL;
      case SUBST_FF: break; // Ignore the literal
      case SUBST_UNASSIGNED:
        mapped_lit = lit; // waterfall!
      default:;
        int mapped_var = VAR_FROM_LIT(mapped_lit);
        // Now evaluate the mapped literal under alpha. If it's unassigned, set it
        switch (peval_lit_under_alpha(mapped_lit)) {
          case FF:
            // We can shorten tautology derivations by marking the reason as assumed.
            // However, we ignore this assumption when doing RAT UP derivations.
            // Only mark literals whose reasons are not already marked
            if (up_reasons[mapped_var] >= 0) {
              up_reasons[mapped_var] |= MSB32;
              add_RAT_marked_var(mapped_var);
            }
            break;
          case TT:;
            // To satisfy the clause, we needed to have derived the truth value of
            // the mapped_lit. Mark the derivation, but do no further checking.
            int reason = up_reasons[mapped_var];
            clear_RAT_marked_vars();
            if (reason >= 0) {
              // Don't store anything in the LSR line because the derivation only
              // includes things in the global and candidate UPs.
              // The RAT check (the caller) will store the (-clause) in the line.
              up_falsified_clause = reason;
              mark_up_derivation();
            }
            return SATISFIED_OR_MUL;
          case UNASSIGNED:
            assume_unit_literal(NEGATE_LIT(mapped_lit));
            break;
          default: PRINT_ERR_AND_EXIT("Corrupted peval value.");
        }
    }
  }

  clear_RAT_marked_vars();
  return 0;
}

// Call when global state == RAT_UP.
// Decrements state back to CANDIDATE_UP.
static void unassume_RAT_clause(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(state != RAT_UP, "state not RAT_UP.");

  // Undo the changes we made to the data structures
  // First, address the unit literals set during new UP
  for (int i = RAT_unit_literals_index; i < unit_literals_size; i++) {
    int lit = unit_literals[i];
    int var = VAR_FROM_LIT(lit);

    // Clear the variable's reason (the generation will clear automatically via bumping)
    up_reasons[var] = -1;
  }

  decrement_state();
}

static void check_sr_line(void) {
  // We save the generation at the start of line checking so we can determine
  // which clauses are marked in the dependency_markings array.
  generation_before_line_checking = alpha_generation;
  alpha_generation++;
  subst_generation++;
  clear_lsr_line();

  // TODO: Minimize witness size

  // TODO: Replace -1/0 with enum/#define
  if (assume_candidate_clause_and_perform_up() == -1) {
    goto candidate_valid;
  }

  // Since we didn't derive UP contradiction, the clause should be nonempty
  PRINT_ERR_AND_EXIT_IF(new_clause_size == 0, "Didn't derive empty clause.");

  // Assumes the witness into the substitution data structure.
  assume_subst(subst_generation);

  // Now do RAT checking
  // printf("c   [%ld] Checking clauses %d to %d\n", current_line + 1, min_clause_to_check, max_clause_to_check);
  int *clause, *next_clause = get_clause_start_unsafe(0);
  int clause_size;
  for (int i = min_clause_to_check; i <= max_clause_to_check; i++) {
    clause = next_clause;
    next_clause = get_clause_start_unsafe(i + 1);
    clause_size = next_clause - clause;

    // Evaluate the clause under the substitution
    switch (reduce_subst_mapped(i)) {
      case NOT_REDUCED:
      case SATISFIED_OR_MUL:
        continue;
      case REDUCED:
        add_RAT_clause_to_lsr_line(i);

        // If the RAT clause is not satisfied, do unit propagation
        if (assume_RAT_clause_under_subst(i) != SATISFIED_OR_MUL) {
          perform_up(alpha_generation);
          PRINT_ERR_AND_EXIT_IF(up_falsified_clause == -1, "No RAT UP contradiction.");
          mark_up_derivation();
          store_RAT_dependencies();
        }

        // Undo the changes we made by (potentially partially) assuming the RAT clause
        unassume_RAT_clause(i);
        alpha_generation++;
        break;
      case CONTRADICTION:
        PRINT_ERR_AND_EXIT("RAT contradiction: should have had UP derivation.");
      default: PRINT_ERR_AND_EXIT("Corrupted reduction value.");
    }    
  }

  print_lsr_line();

  // Congrats - the line checked out! Undo the changes we made to the data structures
candidate_valid:
  unassume_candidate_clause();
  insert_clause_first_last_update(); // Officially add the clause to the formula
  add_wps_and_perform_up();
}

static void process_sr_certificate(void) {
  derived_empty_clause = 0;
  alpha_generation = 1;

  state = GLOBAL_UP;
  add_wps_and_perform_up();

  while (!derived_empty_clause) {
    parse_sr_clause_and_witness(sr_certificate_file);
    // printf("c Parsed line %ld, new clause has size %d and witness with size %d\n", 
    //   current_line + 1, new_clause_size, witness_size);
    resize_sr_trim_data(); 
    check_sr_line();
  }

  fclose(sr_certificate_file);
  if (lsr_proof_file != stdout) {
    fclose(lsr_proof_file);
  }

  printf("s VERIFIED UNSAT\n");
}

int main(int argc, char **argv) {
  if (argc < 3 || argc > 4) {
    print_usage();
    exit(-1);
  }

  parse_cnf(argv[1]);
  init_sr_trim_data();

  printf("c CNF formula claims to have %d clauses and %d variables.\n", formula_size, max_var);

  sr_certificate_file = xfopen(argv[2], "r");
  lsr_proof_file = (argc == 3) ? stdout : xfopen(argv[3], "w");
  process_sr_certificate();
  return 0;
}