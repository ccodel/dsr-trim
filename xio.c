/**
 * @file xio.c
 * @brief "Safer" file I/O operations that error on failure.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-11
 */

#include <stdlib.h>
#include <stdio.h>
#include "global_data.h"
#include "xio.h"

/** Safely opens a file with a path and mode. */
FILE *xfopen(const char * restrict path, const char * restrict mode) {
  FILE *f = fopen(path, mode);
  PRINT_ERR_AND_EXIT_IF(f == NULL, "Unable to open the file");
  return f;
}