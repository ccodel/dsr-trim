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
#include "global_parsing.h"
#include "range_array.h"
#include "xmalloc.h"
#include "sr_parser.h"
#include "logger.h"

////////////////////////////////////////////////////////////////////////////////

void parse_sr_clause_and_witness(FILE *f, srid_t line_num) {
  if (p_strategy == PS_EAGER) {
    ra_commit_empty_ranges_until(&witnesses, line_num);
  } else {
    ra_reset(&witnesses);
  }

  new_clause_size = 0;
  int res, num_times_found_pivot = 0;
  int token, pivot, prev_lit, lit = -1;
  int subst_pair_incomplete = 0;
  uint num_witness_atoms_parsed = 0;

  // Read the SR clause and witness until a 0 is read
  while ((token = read_lit(f)) != 0) {
    prev_lit = lit;
    lit = FROM_DIMACS_LIT(token);

    if (num_times_found_pivot == 0) {
      pivot = lit; // First lit in a nonempty clause is the pivot
      num_times_found_pivot++;
    } else if (lit == pivot) {
      num_times_found_pivot++;
      if (num_times_found_pivot == 3) {
        // The occurrence of the pivot acts as a separator
        // Add it to the witness, but account for a now incomplete "pair"
        subst_pair_incomplete = !subst_pair_incomplete;
      }
    }

    switch (num_times_found_pivot) {
      case 1: // We're reading the clause
        insert_lit(lit);
        new_clause_size++;
        break;
      default: // We're reading the substitution part of the witness
        FATAL_ERR_IF(subst_pair_incomplete && prev_lit == lit,
          "[line %lld] Witness maps literal %d to itself",
          line_num + 1, TO_DIMACS_LIT(lit));
        subst_pair_incomplete = !subst_pair_incomplete;
      case 2:  // We're reading the witness (waterfalls from above)
        FATAL_ERR_IF(VAR_FROM_LIT(lit) > max_var,
          "[line %lld] Var %d out of range.",
          line_num + 1, VAR_FROM_LIT(lit));
        FATAL_ERR_IF(num_times_found_pivot == 2 && lit == NEGATE_LIT(pivot),
          "[line %lld] In the PR part of the witness, the pivot %d maps to FF",
          line_num + 1);
        num_witness_atoms_parsed++;
        ra_insert_int_elt(&witnesses, lit);
        break;
    }
  }

  FATAL_ERR_IF(subst_pair_incomplete,
    "[line %lld] Missing half of subst map.", line_num + 1);

  // Because the witness might get minimized, we add the witness terminator
  if (num_witness_atoms_parsed > 0) {
    ra_insert_int_elt(&witnesses, WITNESS_TERM);
  } else if (num_times_found_pivot > 0) {
    /*
      Along that `num_witness_atoms_parsed == 0`, we know that the clause
      cannot be empty, but it will either be a UP clause or a DRAT clause,
      since we didn't parse any additional witness atoms.
      We need to store the pivot to that during backwrads checking we don't
      need to track the pivot. (Clean up this note later)
    */
    ra_insert_int_elt(&witnesses, pivot);
  }

  ra_commit_range(&witnesses);
  commit_clause();
  // TODO: Remove duplicate literals in the clause or witness?
}
