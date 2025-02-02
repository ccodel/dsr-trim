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

// A flag where 1 indicates that a mapping in the subsitution witness
// hasn't been completely parsed yet.
static int subst_pair_incomplete = 0;

////////////////////////////////////////////////////////////////////////////////

void parse_sr_clause_and_witness(FILE *f, srid_t line_num) {
  if (p_strategy == PS_EAGER) {
    ra_commit_empty_ranges_until(&witnesses, line_num);
  } else {
    ra_reset(&witnesses);
  }

  new_clause_size = 0;
  int res, token, lit, num_times_found_pivot = 0;
  subst_pair_incomplete = 0;
  uint num_witness_atoms_parsed = 0;

  // Read the SR clause and witness until a 0 is read
  while ((token = read_lit(f)) != 0) {
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
        subst_pair_incomplete = !subst_pair_incomplete;
      case 2:  // We're reading the witness (waterfalls from above)
        FATAL_ERR_IF(VAR_FROM_LIT(lit) > max_var, "Var %d out of range.",
          VAR_FROM_LIT(lit));
        num_witness_atoms_parsed++;
        ra_insert_int_elt(&witnesses, lit);
        break;
    }
  }

  FATAL_ERR_IF(subst_pair_incomplete, "Missing half of subst map.");

  // Because the witness might get minimized, we add the witness terminator
  if (num_witness_atoms_parsed > 0) {
    ra_insert_int_elt(&witnesses, WITNESS_TERM);
  }

  ra_commit_range(&witnesses);
  commit_clause();
  // TODO: Remove duplicate literals in the clause or witness?
}
