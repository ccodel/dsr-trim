/**
 * @file php-sr.c
 * @brief A DSR proof generator for the pigeonhole problem.
 * 
 * @author Marijn Heule (marijn@cmu.edu)
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * 
 * @date 2024-04-30
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int num_pigeons;
static int num_holes;
static int with_deletions = 0; // Option to include deletion lines.

// Returns the 1-indexed DIMACS variable for putting pigeon `i` in hole `j`.
static inline int get_php_var(int i, int j) {
  return (i * num_holes) + j + 1;
}

static void print_usage(FILE *f) {
  fprintf(f, "Usage: ./php-sr <num_holes> [-d]\n");
  fprintf(f, "\n\n  where -d adds optional deletion information.\n");
}

int main (int argc, char** argv) {
  if (argc < 2 || argc > 3) {
    print_usage((argc == 1) ? stdout : stderr);
    return (argc != 1);
  }

  if (argc == 3) {
    if (strncmp("-d", argv[2], 3) == 0) {
      with_deletions = 1;
    } else {
      fprintf(stderr, "Incorrect optional argument.\n");
      print_usage(stderr);
      return 1;
    }
  }

  num_holes = atoi(argv[1]);
  num_pigeons = num_holes + 1;

  // The goal is to derive that pigeon i gets assigned to hole i.
  // So for each hole, we compute this derivation.
  // We stop at (num_holes - 1) because the last two pigeons cause UP conflict
  for (int h = 0; h < num_holes - 1; h++) {
    int p;

    // Starting at the last pigeon, loop back until we hit the least unassigned 
    // pigeon (exclusive) and derive that pigeon p doesn't belong in hole h
    for (p = num_holes; p > h; p--) {
      const int v1 = get_php_var(p, h);
      const int v2 = get_php_var(p - 1, h);

      // The SR line claims that pigeon p can't be in hole h
      // We provide a witness saying that pigeon (p - 1) is in hole h instead.
      // Any satisfying assignment to the formula can be constructed for the
      // reduced formula under the substitution by swapping the remaining
      // hole variables.
      printf("-%i -%i %i -%i ", v1, v1, v2, v1);
      for (int j = h + 1; j < num_holes; j++) {
        const int v3 = get_php_var(p - 1, j);
        const int v4 = get_php_var(p , j);
        printf("%i %i %i %i ", v3, v4, v4, v3);
      }

      printf("0\n");

      // After we derive the unit clause (-p), we can delete all
      // binary clauses that contain it
      if (with_deletions) {
        for (int p2 = h; p2 < p; p2++) {
          printf("d -%i -%i 0\n", get_php_var(p2, h), v1);
        }
      }
    }

    // We can now derive the positive unit clause for this pigeon, since
    // all other pigeons are NOT in hole h.
    printf("%i 0\n", get_php_var(p, h));

    // Delete the OR clause containing the unit
    if (with_deletions) {
      printf("d ");
      for (int h2 = 0; h2 < num_holes; h2++) {
        printf("%i ", get_php_var(p, h2));
      }
      printf("0\n");
    }

    // Because pigeon i is in hole i, we know it's not in the other holes    
    for (int j = h + 1; j < num_holes; j++) {
      printf("-%i 0\n", get_php_var(p, j));

      // Delete the unit clauses containing the negated hole variables
      if (with_deletions) {
        for (int p2 = p + 1; p2 < num_pigeons; p2++) {
          printf("d -%i -%i 0\n", get_php_var(p, j), get_php_var(p2, j));
        }
      }
    }
  }

  printf("0\n");
  return 0;
}
