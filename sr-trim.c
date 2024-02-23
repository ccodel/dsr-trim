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

////////////////////////////////////////////////////////////////////////////////

#define INIT_LIT_WP_ARRAY_SIZE   (4)

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

// Array containing the clause ID "reason" causing the variable to be set
static int *up_reasons = NULL;
static int up_reasons_alloc_size = 0; // TODO: use alpha_subst_alloc_size for this?

// A queue of literals to be processed by unit propagation.
static int *up_lits_queue = NULL;
static int up_lits_queue_alloc_size = 0;
static int up_lits_queue_size = 0;

static int derived_empty_clause = 0;

static FILE *sr_certificate_file = NULL;

////////////////////////////////////////////////////////////////////////////////

static void print_usage(void) {
  printf("c Usage: ./sr-trim <cnf-file> <pf-file>\n");
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

  // Allocate space for the lits queue. Probably won't be too large
  up_lits_queue_alloc_size = max_var * 2;
  up_lits_queue = xmalloc(up_lits_queue_alloc_size * sizeof(int));
}

////////////////////////////////////////////////////////////////////////////////

// Sets the literal in the clause to true, assuming it's unit in the clause.
// Then adds the literal's negation to the up_lits_queue array, to look for more unit clauses later.
static void set_unit(int lit, int clause, long gen) {
  printf("  [%d] set %d to unit at %ld\n", clause, lit, gen);
  set_lit_for_alpha(lit, gen);
  up_reasons[VAR_FROM_LIT(lit)] = clause;
  RESIZE_ARR(up_lits_queue, up_lits_queue_alloc_size, up_lits_queue_size, sizeof(int));
  up_lits_queue[up_lits_queue_size++] = NEGATE_LIT(lit);
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

// Performs unit propagation. Returns the clause that caused contradiction, if
// one is found, and -1 otherwise.
// Any literals found are set to the provided generation value.
static int perform_up(long gen) {
  /* The unit propagation algorithm is quite involved and immersed in invariants.
   * Buckle up, cowboys.
   *
   * First, we assume that the literals that have been found to be unit have been
   * set to true in the global partial assignment `alpha`. Then, the negations of
   * those literals have been added to the up_lits_queue. These are the (false)
   * literals that can cause additional clauses to become unit.
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

  // TODO: Better way of doing this, since the size may increase as we do UP?
  for (int i = 0; i < up_lits_queue_size; i++) {
    int lit = up_lits_queue[i];

    // Iterate through its watch pointers and see if the clause becomes unit
    int *wp_list = wps[lit];
    for (int j = 0; j < wp_sizes[lit]; j++) {
      int clause_id = wp_list[j];
      int *clause = get_clause_start(clause_id);
      const int clause_size = get_clause_size(clause_id);
      
      // Lemma: the clause is not a unit clause, and its watch pointers are the first
      //        two literals in the clause (we may reorder literals here)

      // Place the other watch pointer first
      if (clause[0] == lit) {
        clause[0] = clause[1];
        clause[1] = lit;
      }

      int first_wp = clause[0];

      // If the first watch pointer is true, then we can continue to the next wp
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
        j--;       // Need to decrement, since we replaced wp_list[j]
        continue;  
      }

      // We didn't find a replacement watch pointer. Is the first watch pointer false?
      if (peval_lit_under_alpha(first_wp) == FF) {
        return clause_id; // The clause is falsified, so we have a contradiction
      } else {
        set_unit(first_wp, clause_id, LONG_MAX); // Add as a unit literal
      }
    }
  }

  return -1;
}

static void add_wps_and_perform_up(void) {
  // Loop through all clauses. If unit, do UP. Otherwise, add watch pointers.
  int *clause, *next_clause = get_clause_start(0);
  int clause_size;
  for (int i = 0; i < formula_size; i++) {
    clause = next_clause;
    next_clause = get_clause_start(i + 1);
    clause_size = next_clause - clause;

    if (clause_size == 1) {
      // The clause is unit
      // Set its one literal globally to true, and add its negation to the UP queue
      // TODO: Possible set up support for deleting a unit clause (but Marijn says this won't happen)
      int lit = *clause;

      // But first, check if it is set to false - then we derive contradiction immediately
      if (peval_lit_under_alpha(lit) == FF) {
        printf("s VERIFIED UNSAT\n");
        exit(0);
      }

      set_unit(lit, i, LONG_MAX);
    } else {
      // Clause has at least two literals - make them the watch pointers
      add_wp_for_lit(clause[0], i);
      add_wp_for_lit(clause[1], i);
    }
  }

  perform_up(LONG_MAX);
}

static void process_sr_certificate(char *filename) {
  sr_certificate_file = xfopen(filename, "r");
  derived_empty_clause = 0;
  current_generation = 1;

  // Perform initial unit propagation and set up watch pointers
  add_wps_and_perform_up();

  do {
    parse_sr_clause_and_witness(sr_certificate_file);
    
  } while (!derived_empty_clause);

  fclose(sr_certificate_file);
  printf("s VERIFIED UNSAT [end of parsing]\n");
}

int main(int argc, char **argv) {
  if (argc != 3) {
    print_usage();
    exit(-1);
  }

  parse_cnf(argv[1]);
  init_sr_parser();
  init_sr_trim_data();

  printf("c CNF formula claims to have %d clauses and %d variables.\n", formula_size, max_var);

  process_sr_certificate(argv[2]);

  return 0;
}