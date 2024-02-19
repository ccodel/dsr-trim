/**
 * @file sr-trim.c
 * @brief Tool for labeling and trimming SR proof certificates.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-12
 */

#include <stdlib.h>
#include <stdio.h>

#include "global_data.h"
#include "cnf_parser.h"
#include "xmalloc.h"

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "Usage: %s <cnf_file>\n", argv[0]);
    exit(-1);
  }

  parse_cnf(argv[1]);

  return 0;
}