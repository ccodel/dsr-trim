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
#include "xio.h"
#include "global_data.h"
#include "cnf_parser.h"

void parse_cnf(const char *filename) {
  FILE *f = xfopen(filename, "r");

  int res, found_problem_line = 0;
  int num_vars, num_clauses;
  while (!found_problem_line) {
    int c = getc_unlocked(f);
    switch (c) {
      case DIMACS_COMMENT_LINE:
        // Read to the end of the line, discarding the comment
        while (getc_unlocked(f) != '\n') {}
        // res = fscanf(f, "%*[^\n]"); // TODO: More efficient way?
        PRINT_ERR_AND_EXIT_IF(res < 0, "Read error on consuming comment line.");
        break;
      case DIMACS_PROBLEM_LINE:
        found_problem_line = 1;
        res = fscanf(f, "%*s %d %d\n", &num_vars, &num_clauses);
        PRINT_ERR_AND_EXIT_IF(res < 0, "Read error on problem line.");
        break;
      default:
        printf("c Character found was %c\n", c);
        PRINT_ERR_AND_EXIT("Char wasn't a comment or a problem line.");
    }
  }

  if (num_vars <= 0 || num_clauses <= 0) {
    PRINT_ERR_AND_EXIT("The number of variables or clauses wasn't positive.");
  }

  init_global_data(num_clauses, num_vars);

  // Allocate memory
  /*
  witness_buf_size = num_lits * 2;
  witness_buf = xmalloc(witness_buf_size * sizeof(int));

  hints_buf_size = num_cnf_clauses * 2;
  hints_buf = xmalloc(hints_buf_size * sizeof(int));
  */

  // Now parse in the rest of the CNF file
  while (formula_size < num_clauses) {
    // TODO: Assume no more comment lines?
    int parsed_lit = 0, clause_size = 0;
    do {
      READ_NUMERICAL_TOKEN(res, f, &parsed_lit);
      if (parsed_lit == 0) {
        // Sort the literals in the clause before adding it
        // Because no clause should be a tautology, the absolute values are distinct
        int size = get_clause_size(formula_size);
        void *start = ((void *) get_clause_start(formula_size));
        qsort(start, size, sizeof(int), absintcompare);
        insert_clause();
      } else {
        int lit = FROM_DIMACS_LIT(parsed_lit);
        insert_lit(lit);
      }
    } while (parsed_lit != 0);
  }

  fclose(f);
}

void print_cnf(void) {
  for (int c = 0; c < formula_size; c++) {
    int *clause_ptr = get_clause_start(c);
    int *clause_end = get_clause_start(c + 1);
    for (; clause_ptr < clause_end; clause_ptr++) {
      printf("%d ", TO_DIMACS_LIT(*clause_ptr));
    }
    printf("0\n");
  }
}