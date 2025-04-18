/**
 * @file lsr_err.c
 * @brief Verbose error messages for `lsr-check`.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-04-16
 */

#include <stdlib.h>
#include "lsr_data.h"
#include "lsr_err.h"
#include "../global_data.h"
#include "../logger.h"

#define LOG_MORE_INFO_MSG()  \
  log_err_raw("c (For more information about this error, run with the `-V` option.)\n")

static void print_assignment_and_subst(void) {
    log_err_raw("c The active partial assignment: ");
    dbg_print_assignment();
    log_err_raw("c The current substitution: ");
    dbg_print_subst();
}

static void print_candidate_assignment_and_subst(void) {
  log_err_raw("c The candidate redundant clause: ");
  dbg_print_clause(CLAUSE_ID_FROM_LINE_NUM(current_line));
  print_assignment_and_subst();
}

void lsr_err_no_rat_hint_group(srid_t clause_id) {
  srid_t parsed_line_id = get_line_id_for_line_num(current_line);
  srid_t line_id = LINE_ID_FROM_LINE_NUM(current_line);
  log_err("[line %lld | id %lld] "
    "RAT clause %lld has no corresponding RAT hint group.",
    parsed_line_id, line_id, TO_DIMACS_CLAUSE(clause_id));

  switch (err_verbosity_level) {
    case VL_VERBOSE:
      print_candidate_assignment_and_subst();
    case VL_NORMAL: // waterfalls from above
      log_err_raw("c The supposed RAT clause: ");
      dbg_print_clause(clause_id);
      log_err_raw("c The RAT clause, under the substitution: ");
      dbg_print_clause_under_subst(clause_id);
      if (get_num_RAT_hints() > 0) {
        log_err_raw("\nc The clauses marked as RAT by negative hints:\n");
        srid_t *hints_iter = get_hints_start();
        srid_t *hints_end = get_hints_end();
        for (; hints_iter < hints_end; hints_iter++) {
          srid_t hint = *hints_iter;
          if (hint < 0) {
            log_err_raw("%lld ", CLAUSE_ABS(hint));
          }
        }
        log_err_raw("\n");
      } else {
        log_err_raw("c Line %lld had no RAT hints, so we expected "
          "a direct RUP contradiction.\n",
          parsed_line_id);
        srid_t last_up_hint = *(get_hints_end() - 1);
        log_err_raw("c We expected contradiction on the last UP hint %lld.\n",
          TO_DIMACS_CLAUSE(last_up_hint));
        log_err_raw("c Last unit hint, clause %lld: ",
          TO_DIMACS_CLAUSE(last_up_hint));
        dbg_print_clause(last_up_hint);
        log_err_raw("c Last unit, under the assignment: ");
        dbg_print_clause_under_alpha(last_up_hint);
      }
      break;
    default: LOG_MORE_INFO_MSG();
  }

  exit(1);
}

/**
 * @brief Prints an error message when a RAT clause `clause_id` does not
 *        derive unit propagation contradiction on hint `contra_hint`.
 * 
 * @param clause_id The clause ID of the RAT clause.
 * @param contra_hint The (positive) hint that was supposed to derive
 *                    contradiction. If the hint group has no UP hints,
 *                    this is usually equal to `clause_id`.
 */
void lsr_err_no_up_contradiction(srid_t clause_id, srid_t contra_hint) {
  srid_t parsed_line_id = get_line_id_for_line_num(current_line);
  srid_t line_id = LINE_ID_FROM_LINE_NUM(current_line);
  log_err("[line %lld | id %lld] "
    "Unit prop on RAT clause %lld didn't derive contradiction.",
    parsed_line_id, line_id, TO_DIMACS_CLAUSE(clause_id));

  switch (err_verbosity_level) {
    case VL_VERBOSE:
      print_candidate_assignment_and_subst();
    case VL_NORMAL: // waterfalls from above
      log_err_raw("c RAT clause %lld without a UP contradiction derivation: ",
        TO_DIMACS_CLAUSE(clause_id));
      dbg_print_clause(clause_id);
      if (contra_hint > 0) {
        log_err_raw(
          "c The final hint (clause %lld), supposed to evaluate to false: ",
          contra_hint);
        dbg_print_clause(FROM_DIMACS_CLAUSE(contra_hint));
        log_err_raw("c Clause %lld, under the assignment: ",
          contra_hint);
        dbg_print_clause_under_alpha(FROM_DIMACS_CLAUSE(contra_hint));
        log_err_raw("c (The clause contains all FF/one TT because"
          " it was unit and was added to the assignment.)\n");
      } else {
        log_err_raw("c There seemed to be no hints for RAT clause %lld."
          " Is this intentional?\n",
          TO_DIMACS_CLAUSE(clause_id));
      }
      break;
    default: LOG_MORE_INFO_MSG();
  }

  exit(1);
}