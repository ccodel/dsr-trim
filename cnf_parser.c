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
#include "cnf_parser.h"

void parse_cnf(FILE *f) {
  int res, found_problem_line = 0;
  int num_vars, num_clauses;
  while (!found_problem_line) {
    int c = getc_unlocked(f);
    switch (c) {
      case DIMACS_COMMENT_LINE:
        // Read to the end of the line, discarding the comment
        while (getc_unlocked(f) != '\n') {}
        break;
      case DIMACS_PROBLEM_LINE:
        found_problem_line = 1;
        res = fscanf(f, " cnf %d %d\n", &num_vars, &num_clauses);
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
    int parsed_lit = 0, clause_size = 0;
    do {
      READ_NUMERICAL_TOKEN(res, f, &parsed_lit);
      if (parsed_lit != 0) {
        int lit = FROM_DIMACS_LIT(parsed_lit);
        insert_lit(lit);
        clause_size++;
      }
    } while (parsed_lit != 0);

    if (clause_size == 0) {
      derived_empty_clause = 1;
      break;
    } else if (clause_size == 1) {
      insert_clause();
      continue;
    }

    // Now we sort the literals in the clause
    // Then, we efficiently remove duplicate literals and detect tautologies
    // Tautological clauses are added but are deleted, leaving a "hole"
    int *write_ptr, *read_ptr = get_clause_start(formula_size);
    qsort((void *) read_ptr, clause_size, sizeof(int), intcmp);
    int is_tautology = 0;
    int skipped_lits = 0;
    int lit, next_lit = read_ptr[0];

    for (int i = 0; i < clause_size - 1; i++) {
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

    // Write the last literal
    // This can "write" a duplicate, if the duplicates ended the clause
    // But the writing is "erased" when the lits_db_size is adjusted below
    if (skipped_lits > 0) {
      *write_ptr = next_lit;
    }

    if (!is_tautology) {
      lits_db_size -= skipped_lits; // Update the clause's size before adding
      insert_clause();
    } else {
      lits_db_size -= clause_size;
      insert_clause();
      delete_clause(formula_size - 1);
    }
  }

  fclose(f);
}

void print_cnf(void) {
  for (int c = 0; c < formula_size; c++) {
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