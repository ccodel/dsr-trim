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

static int subst_pair_incomplete = 0;

////////////////////////////////////////////////////////////////////////////////

void init_sr_parser(void) {
  witness_alloc_size = max_var * 2;
  witness_size = 0;
  witness = xmalloc(witness_alloc_size * sizeof(int));
}

static inline void insert_witness_lit(int lit) {
  // TODO: Can be more restrictive by saving "max_var" before parsing the new clause
  // Can also restrict the first lit in a subst pair to be a positive val (a var)
  PRINT_ERR_AND_EXIT_IF(VAR_FROM_LIT(lit) > max_var, "Variable out of range.");
  RESIZE_ARR(witness, witness_alloc_size, witness_size, sizeof(int));
  witness[witness_size++] = lit;
}

void parse_sr_clause_and_witness(FILE *f) {
  witness_size = new_clause_size = 0;
  int res, token, lit, num_times_found_pivot = 0;
  subst_index = INT_MAX;
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
      if (num_times_found_pivot == 3) {
        // The third time we see the pivot, it's as a separator
        goto read_next_token;
      }
    }

    // TODO: Allow for a witness that only has a substitution portion
    // Marijn suggests using a thrice-repeated pivot as a marker for this
    switch (num_times_found_pivot) {
      case 1: // We're reading the clause
        insert_lit_no_first_last_update(lit);
        new_clause_size++;
        break;
      default: // We're reading the substitution part of the witness (waterfall!)
        subst_index = (subst_index == INT_MAX) ? witness_size : subst_index;
        subst_pair_incomplete = !subst_pair_incomplete;
      case 2: // We're reading the witness (waterfalls from above)
        insert_witness_lit(lit);
        break;
    }

read_next_token:
    READ_NUMERICAL_TOKEN(res, f, &token);
  }

  if (subst_pair_incomplete) {
    PRINT_ERR_AND_EXIT("Missing second half of subst mapping pair.");
  }

  if (subst_index == INT_MAX) {
    subst_index = witness_size;
  }
}
