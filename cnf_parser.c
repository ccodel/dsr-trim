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

int parse_clause(FILE *f) {
  new_clause_size = 0;
  int parsed_lit = 0;
  while ((parsed_lit = read_lit(f)) != 0) {
    int lit = FROM_DIMACS_LIT(parsed_lit);
    insert_lit_no_first_last_update(lit);
    new_clause_size++;
  }

  if (new_clause_size <= 1) {
    return 0;
  }

  // Now we sort the literals in the clause
  // Then, we efficiently remove duplicate literals and detect tautologies
  int *write_ptr, *read_ptr = get_clause_start(formula_size);
  qsort((void *) read_ptr, new_clause_size, sizeof(int), intcmp);
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
  srid_t num_clauses;
  int res, num_vars, found_problem_line = 0;
  while (!found_problem_line) {
    int c = getc_unlocked(f);
    switch (c) {
      case DIMACS_COMMENT_LINE:
        // Read to the end of the line, discarding the comment
        while (getc_unlocked(f) != '\n') {}
        break;
      case DIMACS_PROBLEM_LINE:
        found_problem_line = 1;
        res = fscanf(f, CNF_HEADER_STR, &num_vars, &num_clauses);
        PRINT_ERR_AND_EXIT_IF(res < 0, "Read error on problem line.");
        break;
      default:
        PRINT_ERR_AND_EXIT("Char wasn't a comment or a problem line.");
    }
  }

  if (num_vars <= 0 || num_clauses <= 0) {
    PRINT_ERR_AND_EXIT("The number of variables or clauses wasn't positive.");
  }

  init_global_data(num_clauses, num_vars);

  // Now parse in the rest of the CNF file
  // We assume that no more comment lines can appear, and will error if a non-number is parsed
  while (formula_size < num_clauses) {
    int is_tautology = parse_clause(f);
    if (new_clause_size == 0) {
      derived_empty_clause = 1;
      insert_clause();
      break;
    } else if (is_tautology) {
      insert_clause();
      delete_clause(formula_size - 1);
    } else {
      insert_clause_first_last_update();
    }
  }

  fclose(f);
}

void print_cnf(void) {
  for (srid_t c = 0; c < formula_size; c++) {
    if (is_clause_deleted(c)) {
      continue;
    }

    int *clause_ptr = get_clause_start(c);
    int *clause_end = get_clause_start(c + 1);
    for (; clause_ptr < clause_end; clause_ptr++) {
      printf("%d ", TO_DIMACS_LIT(*clause_ptr));
    }
    printf("0\n");
  }
}