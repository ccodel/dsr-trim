/**
 * @file compress.c
 * @brief A compressor for DSR and LSR files.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-04-02
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

#define INIT_SIZE    (10000)
#define ZEROS_FOR_ADDITION    (2)
#define ZEROS_FOR_DELETION    (1)

////////////////////////////////////////////////////////////////////////////////

static FILE *input, *output;

/** @brief A single flat array for the input data.
 *  
 * The input data may arrive with unordered lines with holes in the line ids.
 * Thus, we store the data as it arrives, but fix its order with the
 * `data_mappings` array (see below).
 */
static srid_t *data = NULL;

// Logical size of the `data` array. The number of elements it contains.
static srid_t data_size = 0;

// The allocated size of the `data` array through `malloc()`.
static srid_t data_alloc_size = 0;

/** @brief Indexes into `data`, implicitly ordered by the parsed line ids. 
 * 
 * The input data can arrive unordered, in the sense that line 20 can appear
 * before line 5. The indexes of where the line data appears in `data` are
 * stored in `data_mappings`.
 * 
 * Because both an addition and a deletion line can appear with the same line
 * id, indexes are bit-shifted by 1, with deletion acting as a LSB flag.
 * 
 * Most LSR files start their line ids after the number of clauses in the
 * associated formula, which might be quite high. As a result, the first
 * part of `data_mappings` will be all empty.
 * 
 * Entries are initialized to -1.
 */
static srid_t *data_mappings = NULL;

// The allocated size of `data_mappings` through `malloc()`.
static srid_t data_mappings_alloc_size = 0;

#ifdef LONGTYPE
static srid_t min_line_id = LLONG_MAX;
#else
static srid_t min_line_id = INT_MAX;
#endif

static srid_t max_line_id = -1;

// Flag for whether the input file is in LSR or DSR format.
// By default, assume the input file is in LSR format.
static int read_lsr = 1;

////////////////////////////////////////////////////////////////////////////////

static void print_usage(FILE *f) {
  fprintf(f, "Usage: ./compress <input_file> [output_file] [option]\n\n");
  fprintf(f, "where [option] is one of the following:\n\n");
  fprintf(f, "  -d    Compress a DSR file.\n");
  fprintf(f, "  -l    Compress an LSR file. (This is the default behavior.)\n\n");
  fprintf(f, "When an output file is not provided, stdout is used.\n");
  fprintf(f, "\n");
}

// Allocates and initializes the `data` and `data_mappings` arrays.
static void init_data(void) {
  // No need to allocate any memory if reading a DSR file.
  if (read_lsr) {
    data_alloc_size = INIT_SIZE;
    data = xmalloc(data_alloc_size * sizeof(srid_t));

    data_mappings_alloc_size = INIT_SIZE;
    data_mappings = xrealloc_memset(data_mappings, 0,  
      data_mappings_alloc_size * sizeof(srid_t), 0xff);
  }
}

static inline void store_atom(srid_t atom) {
  RESIZE_ARR(data, data_alloc_size, data_size, sizeof(srid_t));
  data[data_size++] = atom;
}

// Compresses the DSR input file.
// Because DSR files are not "ordered", we can directly write what we read.
static void compress_dsr_input(void) {
  srid_t token;
  while (has_another_line(input)) {
    int line_type = read_dsr_line_start(input);
    write_dsr_line_start(output, (line_type == DELETION_LINE) ? 1 : 0);

    // Keep reading atoms until 0 is read
    do {
      token = read_clause_id(input);
      write_clause_id(output, token);
    } while (token != 0);
  }
}

static void compress_lsr_input(void) {
  srid_t token, line_id;
  while (has_another_line(input)) {
    int line_type = read_lsr_line_start(input, &line_id);
    int zeros_left = (line_type == ADDITION_LINE) ? 
      ZEROS_FOR_ADDITION : ZEROS_FOR_DELETION;
    min_line_id = MIN(min_line_id, line_id);
    max_line_id = MAX(max_line_id, line_id);
    
    // Check that this line type and line ID doesn't exist in the mappings yet
    PRINT_ERR_AND_EXIT_IF(line_id < 0, "Line id is negative.");
    srid_t mapping = (line_id << 1) | ((line_type == ADDITION_LINE) ? 0 : 1);

    if (mapping >= data_mappings_alloc_size) {
      srid_t old_size = data_mappings_alloc_size;
      RESIZE_MEMSET_ARR(data_mappings, data_mappings_alloc_size,
        mapping, sizeof(srid_t), 0xff);
    }

    PRINT_ERR_AND_EXIT_IF(data_mappings[mapping] != -1, "Map already exists.");
    
    // Now store where the data for this line starts
    data_mappings[mapping] = data_size;

    // Keep reading and storing atoms until enough zeros are read
    while (zeros_left > 0) {
      token = read_lit(input);
      store_atom(token);
      if (token == 0) {
        zeros_left--;
      }
    }
  }

  // Now that all input has been read, write it back out
  // Follow the ordering in data_mappings: for each line id, add before del
  for (srid_t i = (min_line_id << 1); i <= ((max_line_id << 1) | 1); i++) {
    if (data_mappings[i] != -1) {
      int is_deletion_line = (i & 1);
      srid_t line_id = i >> 1;
      int zeros_left = (is_deletion_line) ? ZEROS_FOR_DELETION : ZEROS_FOR_ADDITION;
      srid_t *data_ptr = data + data_mappings[i];

      write_lsr_line_start(output, line_id, is_deletion_line);
      while (zeros_left > 0) {
        srid_t atom = *data_ptr++;
        write_clause_id(output, atom);
        if (atom == 0) {
          zeros_left--;
        }
      }
    }
  }
}

int main(int argc, char *argv[]) {
  if (argc < 2 || argc > 4) {
    print_usage((argc == 1) ? stdout : stderr);
    return (argc != 1);
  }

  // Open the files right away, so we fail fast if they don't exist.
  input  = xfopen(argv[1], "r");
  if (argc == 2 || argv[2][0] == '-') {
    output = stdout;
    optind = 2;
  } else {
    output = xfopen(argv[2], "w");
    optind = 3;
  }

  // TODO: Allow for sorting flag
  int opt; 
  while ((opt = getopt(argc, argv, "dl")) != -1) {
    switch (opt) {
      case 'd':
        printf("c Mode switched to DSR compression.\n");
        read_lsr = 0;
        break;
      case 'l': read_lsr = 1; break;
      default: 
        fprintf(stderr, "Error: Unknown option: %c\n", opt);
        print_usage(stderr);
        return 1;
    }
  }

  read_binary = 0;
  write_binary = 1;
  init_data();

  if (read_lsr) {
    compress_lsr_input();
  } else {
    compress_dsr_input();
  }

  return 0;
}