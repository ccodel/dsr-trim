/**
 * @file cnf_parser.c
 * @brief Parses CNF formulas and stores them in global data structures.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-11
 */

#include <stdlib.h>
#include <stdio.h>

#include "xmalloc.h"
#include "global_data.h"
#include "global_parsing.h"
#include "cnf_parser.h"
#include "logger.h"

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Consumes and parses a single new clause from the CNF file `f`.
 *        Returns `1` if the clause is a tautology, and `0` otherwise.
 * 
 * The newly consumed and parsed clause is stored in the literals database
 * `lits_db`, but the new clause is not committed. This allows the caller
 * to handle tautologies and potentially remove the uncommitted clause.
 * The number of parsed literals is stored in `new_clause_size`.
 * 
 * The new clause will have its literals sorted in increasing order of
 * magnitude, and duplicate literals will be removed.
 * 
 * This function does NOT adjust the clause's first/last literal values.
 * To do that, the caller must call `commit_clause_with_first_last_update()`.
 * Also see `lits_first_last_clauses` in `global_data.h`.
 * 
 * Any comment lines before the start of the clause, or appearing between
 * literals of the clause, are consumed and ignored. Note: comment lines may
 * appear at any point, as long as they appear on their own line starting
 * with a `'c'`. Comments after the ending of the clause are not consumed.
 * 
 * If the clause is a tautology (i.e., a `1` is returned), then
 * 
 * @param f The file stream to parse a clause from.
 * @return `1` if the clause is a tautology, and `0` otherwise.
 */
int parse_clause(FILE *f) {
  // Since we're parsing a new clause, reset the global variable
  new_clause_size = 0;

  // Parse literals until we see an ending `0`
  int parsed_lit = 0;
  while ((parsed_lit = read_formula_lit(f)) != 0) {
    int lit = FROM_DIMACS_LIT(parsed_lit);
    insert_lit(lit);
  }

  return sort_and_dedup_new_cnf_clause();
}

void parse_cnf(FILE *f) {
  int c, res, found_problem_line = 0;
  while (!found_problem_line) {
    switch ((c = getc_unlocked(f))) {
      case DIMACS_COMMENT_LINE:
        // Read to the end of the line, discarding the comment
        while (getc_unlocked(f) != '\n') {}
        break;
      case DIMACS_PROBLEM_LINE:
        found_problem_line = 1;
        res = fscanf(f, CNF_HEADER_STR, &num_cnf_vars, &num_cnf_clauses);
        FATAL_ERR_IF(res < 0, "Read error on problem header line.");
        break;
      default:
        log_fatal_err("Char %c wasn't a comment or a problem line.", c);
    }
  }

  FATAL_ERR_IF(num_cnf_vars <= 0,
    "The number of vars in the header (%d) was not positive.", num_cnf_vars);
  FATAL_ERR_IF(num_cnf_clauses <= 0,
    "The number of clauses in the header (%d) was not positive.", num_cnf_clauses);

  // Formula parsing requires that newlines are left unconsumed until
  // the next call to `parse_formula_lit()`. This allows the parser 
  // to know where valid comment lines occur (i.e., after a newline).
  // We add the newline here to maintain this invariant.
  ungetc('\n', f);

  init_global_data();

  // Now parse the rest of the CNF file.
  // Any intervening comment lines are ignored. (See `read_formula_lit()`.)
  while (formula_size < num_cnf_clauses) {
    int is_tautology = parse_clause(f);
    if (new_clause_size == 0) {
      log_fatal_err("The empty clause was found at clause %lld in the CNF.",
        TO_DIMACS_CLAUSE(formula_size));
    } else if (is_tautology) {
      logc("Tautology in clause %lld detected, deleting...", formula_size);
      commit_and_delete_clause();
    } else {
      commit_clause();
    }
  }

  fclose(f);

  logc("The CNF formula has %lld clauses and %d variables.",
    formula_size, num_cnf_vars);
}
