/**
 * @file php.c
 * @brief Generates CNF files for the pigeonhole problem.
 * 
 * @author Marijn Heule (marin@cmu.edu)
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * 
 * @date 2024-04-30
 */

#include <stdio.h>
#include <stdlib.h>

static int num_holes;
static int num_pigeons;

// Returns the 1-indexed DIMACS variable for putting pigeon `i` in hole `j`.
static inline int get_php_var(int i, int j) {
  return (i * num_holes) + j + 1;
}

void print_usage(FILE *f) {
  fprintf(f, "Usage: ./php <num_holes>\n");
}

int main (int argc, char* argv[]) {
  if (argc != 2) {
    print_usage((argc == 1) ? stdout : stderr);
    return (argc != 1);
  }

  num_holes = atoi(argv[1]);
  num_pigeons = num_holes + 1;
  int num_vars = num_pigeons * num_holes;
  int num_clauses = num_pigeons + num_pigeons * num_holes * num_holes / 2;

  printf("p cnf %i %i\n", num_vars, num_clauses);

  // At least one pigeon per hole
  // For each pigeon, at least one of its hole vars has to be true
  for (int i = 0; i < num_pigeons; ++i) {
    for (int j = 0; j < num_holes; ++j)
      printf("%i ", get_php_var(i, j));
    printf("0\n");
  }

  // At most one pigeon per hole
  // For each hole, it is not the case that two different pigeons are in it
  for (int hole = 0; hole < num_holes; ++hole) {
    for (int p1 = 0; p1 < num_pigeons; ++p1) {
      for (int p2 = p1 + 1; p2 < num_pigeons; ++p2) {
        printf("-%i -%i 0\n", 
          get_php_var(p1, hole), get_php_var(p2, hole));
      }
    }
  }

  return 0;
}
