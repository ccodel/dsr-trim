/**
 * @file xio.c
 * @brief "Safer" file I/O operations that error on failure.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-11
 */

#include <stdlib.h>
#include <stdio.h>
#include "xio.h"

/** Safely opens a file with a path and mode. */
FILE *xfopen(const char * restrict path, const char * restrict mode) {
  FILE *f = fopen(path, mode);
  if (f == NULL) {
    fprintf(stderr, "c Error: Unable to open the file %s\n", path);
    exit(-1);
  }

  return f;
}
