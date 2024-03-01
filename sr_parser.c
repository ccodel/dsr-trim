/**
 * @file sr_parser.c
 * @brief Parser for SR certificate and LSR proof files.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-19
 */

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>

#include "global_data.h"
#include "xmalloc.h"
#include "sr_parser.h"

////////////////////////////////////////////////////////////////////////////////

int *witness = NULL;
int witness_size = 0;
int witness_alloc_size = 0;
int pivot = 0;
int new_clause_size = 0;
int subst_index = 0;

int min_clause_to_check = 0;
int max_clause_to_check = 0;

static int subst_pair_incomplete = 0;

////////////////////////////////////////////////////////////////////////////////

void init_sr_parser(void) {
  witness_alloc_size = max_var * 2;
  witness_size = 0;
  witness = xmalloc(witness_alloc_size * sizeof(int));
}

static void set_min_and_max_clause_to_check(int lit) {
  update_first_last_clause(lit);
  if (lits_first_clause[lit] != -1) {
    min_clause_to_check = MIN(min_clause_to_check, lits_first_clause[lit]); 
    max_clause_to_check = MAX(max_clause_to_check, lits_last_clause[lit]);
  }
}

static void insert_witness_lit(int lit) {
  // Resize if inserting the literal would exceed the allocated size
  RESIZE_ARR(witness, witness_alloc_size, witness_size, sizeof(int));
  witness[witness_size] = lit;
  witness_size++;

  // If we are reading in UP literals, or the first half of a subst mapping
  if (subst_index == INT_MAX) {
    // Since a UP literal is set to true in the witness, clauses with the
    // negation of the literal get reduced, so must be checked
    int neg_lit = NEGATE_LIT(lit);
    set_min_and_max_clause_to_check(neg_lit);
  } else if (subst_pair_incomplete) {
    // If a mapping, we need to check both lit and its negation
    int neg_lit = NEGATE_LIT(lit);
    set_min_and_max_clause_to_check(lit);
    set_min_and_max_clause_to_check(neg_lit);
  }
}

void parse_sr_clause_and_witness(FILE *f) {
  witness_size = new_clause_size = 0; // Clear extern sr_parser data
  int res, token, lit, num_times_found_pivot = 0;
  subst_index = INT_MAX;
  min_clause_to_check = INT_MAX;
  max_clause_to_check = 0;
  subst_pair_incomplete = 0;

  // Read the SR clause and witness until a 0 is read
  READ_NUMERICAL_TOKEN(res, f, &token);
  while (token != 0) {
    lit = FROM_DIMACS_LIT(token);
    if (num_times_found_pivot == 0) {
      pivot = lit; // First lit in a nonempty clause is the pivot
      num_times_found_pivot++;
    } else if (lit == pivot) {
      num_times_found_pivot++;
    }

    switch (num_times_found_pivot) {
      case 1: // We're reading the clause
        insert_lit_no_first_last_update(lit);
        new_clause_size++;
        break;
      case 3: // We're reading the substitution part of the witness (waterfall!)
        subst_index = (subst_index == INT_MAX) ? witness_size : subst_index;
        subst_pair_incomplete = !subst_pair_incomplete;
      case 2: // We're reading the witness (waterfalls from above)
        insert_witness_lit(lit);
        break;
      default: PRINT_ERR_AND_EXIT("Seen pivot more than 3 times.");
    }

    READ_NUMERICAL_TOKEN(res, f, &token);
  }

  if (subst_pair_incomplete) {
    PRINT_ERR_AND_EXIT("Missing second half of subst mapping pair.");
  }

  if (subst_index == INT_MAX) {
    subst_index = witness_size;
  }

  // TODO: Reject tautologies
}
