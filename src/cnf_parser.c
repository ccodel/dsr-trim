/**
 * @file cnf_parser.c
 * @brief Parses CNF files and stores them in global data structures.
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

int parse_clause(FILE *f) {
  new_clause_size = 0;
  int parsed_lit = 0;
  while ((parsed_lit = read_lit(f)) != 0) {
    int lit = FROM_DIMACS_LIT(parsed_lit);
    insert_lit(lit);
    new_clause_size++;
  }

  // TODO: Pull this out into helper for sr_parser?
  int *write_ptr, *read_ptr = get_clause_start(formula_size);
  if (new_clause_size <= 1) {
    return 0;
  }

  // Now we sort the literals in the clause
  // Then, we efficiently remove duplicate literals and detect tautologies
  qsort((void *) read_ptr, new_clause_size, sizeof(int), absintcmp);
  int is_tautology = 0;
  int skipped_lits = 0;
  int lit, next_lit = read_ptr[0];

  for (int i = 0; i < new_clause_size - 1; i++) {
    read_ptr++;
    lit = next_lit;
    next_lit = *read_ptr;

    if (lit == next_lit) {
      skipped_lits++;
      if (skipped_lits == 1) {
        write_ptr = read_ptr - 1;
      }
    } else if (lit == NEGATE_LIT(next_lit)) {
      is_tautology = 1;
      break;
    } else if (skipped_lits > 0) {
      *write_ptr = lit;
      write_ptr++;
    }
  }

  // Write the last literal - this could "write" a duplicate
  // However, the duplicate is "erased" when the lits_db_size is adjusted below
  if (skipped_lits > 0) {
    *write_ptr = next_lit;
  }

  new_clause_size -= skipped_lits;
  lits_db_size -= skipped_lits;
  return is_tautology;
}

void parse_cnf(FILE *f) {
  int res, found_problem_line = 0;
  while (!found_problem_line) {
    int c = getc_unlocked(f);
    switch (c) {
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
        log_fatal_err("Char wasn't a comment or a problem line.");
    }
  }

  FATAL_ERR_IF(num_cnf_vars <= 0,
    "The problem header variable number (%d) was not positive.", num_cnf_vars);
  FATAL_ERR_IF(num_cnf_clauses <= 0,
    "The problem header clause number (%d) was not positive.", num_cnf_clauses);

  init_global_data();

  // Now parse in the rest of the CNF file
  // We assume that no more comment lines can appear
  while (formula_size < num_cnf_clauses) {
    int is_tautology = parse_clause(f);
    if (new_clause_size == 0) {
      log_fatal_err("The empty clause was found at clause %lld in the CNF.",
        formula_size);
    } else if (is_tautology) {
      logc("Tautology in clause %lld detected, deleting...", formula_size);
      commit_clause();
      delete_clause(formula_size - 1);
    } else {
      commit_clause_with_first_last_update();
    }
  }

  fclose(f);

  logc("The CNF formula has %lld clauses and %d variables.",
    formula_size, max_var);
}

void print_cnf(void) {
  for (srid_t c = 0; c < formula_size; c++) {
    if (is_clause_deleted(c)) {
      continue;
    }

    int *clause_iter = get_clause_start(c);
    int *clause_end = get_clause_start(c + 1);
    for (; clause_iter < clause_end; clause_iter++) {
      log_raw(VL_NORMAL, "%d ", TO_DIMACS_LIT(*clause_iter));
    }
    log_raw(VL_NORMAL, "0\n");
  }
}