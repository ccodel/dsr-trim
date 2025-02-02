/**
 * @file decompress.c
 * @brief A decompressor for DSR and LSR files.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-04-07
 */

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>
#include <unistd.h>

#include "xio.h"
#include "xmalloc.h"
#include "global_data.h"
#include "global_parsing.h"
#include "logger.h"

#define INIT_SIZE    (10000)
#define ZEROS_FOR_ADDITION    (2)
#define ZEROS_FOR_DELETION    (1)

static int read_lsr = 1;

////////////////////////////////////////////////////////////////////////////////

static FILE *input, *output;

static void print_usage(FILE *f) {
  fprintf(f, "Usage: ./decompress <input_file> [output_file] [option]\n\n");
  fprintf(f, "where [option] is one of the following:\n\n");
  fprintf(f, "  -d   Decompress a DSR file.\n");
  fprintf(f, "  -l   Decompress an LSR file. (This is the default behavior.)\n\n");
  fprintf(f, "When an output file is not provided, stdout is used.\n");
  fprintf(f, "\n");
}

static void decompress_dsr_input(void) {
  srid_t token;
  while (has_another_line(input)) { 
    int line_type = read_dsr_line_start(input);
    if (line_type == DELETION_LINE) {
      write_dsr_deletion_line_start(output);
    } else {
      write_dsr_addition_line_start(output);
    }

    // Keep reading atoms until 0 is read
    while ((token = read_clause_id(input)) != 0) {
      write_clause_id(output, token);
    }

    write_sr_line_end(output);
  }
}

static void decompress_lsr_input(void) {
  srid_t token, line_id;
  while (has_another_line(input)) {
    int line_type = read_lsr_line_start(input, &line_id);
    FATAL_ERR_IF(line_id < 0, "Negative line id encountered.");
    int zeros_left = (line_type == ADDITION_LINE) ? 
      ZEROS_FOR_ADDITION : ZEROS_FOR_DELETION;

    if (line_type == DELETION_LINE) {
      write_lsr_deletion_line_start(output, line_id);
    } else {
      write_lsr_addition_line_start(output, line_id);
    }

    // Keep reading atoms until enough zeros are read
    while (zeros_left > 0) {
      token = read_clause_id(input);
      if (token == 0) {
        zeros_left--;
      }

      if (zeros_left > 0) {
        write_clause_id(output, token);
      }
    }

    write_sr_line_end(output);
  }
}

int main(int argc, char *argv[]) {
  if (argc < 2 || argc > 4) {
    print_usage((argc == 1) ? stdout : stderr);
    return (argc != 1);
  }

  // Open the files right away, so we fail fast if they don't exist
  input  = xfopen(argv[1], "r");
  if (argc == 2 || argv[2][0] == '-') {
    output = stdout;
    optind = 2;
  } else {
    output = xfopen(argv[2], "w");
    optind = 3;
  }

  int opt;
  while ((opt = getopt(argc, argv, "dl")) != -1) {
    switch (opt) {
      case 'd':
        logc("Mode switched to DSR decompression.");
        read_lsr = 0;
        break;
      case 'l': read_lsr = 1; break;
      default:
        log_err("Unknown option: %c", opt);
        print_usage(stderr);
        return 1;
    }
  }

  read_binary = 1;
  write_binary = 0;
  
  if (read_lsr) {
    decompress_lsr_input();
  } else {
    decompress_dsr_input();
  }
}