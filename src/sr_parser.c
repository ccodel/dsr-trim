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
  int res, token, lit, pivot, num_times_found_pivot = 0;
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
        FATAL_ERR_IF(VAR_FROM_LIT(lit) > max_var,
          "[line %lld] Var %d out of range.",
          line_num + 1, VAR_FROM_LIT(lit));
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

void dbg_print_witness(srid_t line_num) {
  int *witness_iter = get_witness_start(line_num);
  int *witness_end = get_witness_end(line_num);

  log_raw(VL_NORMAL, "[line %lld] Witness: ", line_num + 1);
  for (; witness_iter < witness_end; witness_iter++) {
    int lit = *witness_iter;
    switch (lit) {
      case WITNESS_TERM: witness_iter = witness_end;          break;
      case SUBST_FF: log_raw(VL_NORMAL, "FF ");               break;
      case SUBST_TT: log_raw(VL_NORMAL, "TT ");               break;
      default: log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(lit)); break;
    }
  }

  log_raw(VL_NORMAL, "0\n");
}