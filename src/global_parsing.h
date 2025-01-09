/**
 * @file global_parsing.h
 * @brief A collection of common parsing functions for DIMACS CNF/DSR/LSR files.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-04-02
 */

#ifndef _GLOBAL_PARSING_H_
#define _GLOBAL_PARSING_H_

#include "global_data.h"
#include <stdio.h>

/** DIMACS character that starts a comment line. */
#define DIMACS_COMMENT_LINE ('c')

/** DIMACS character that starts a problem line. */
#define DIMACS_PROBLEM_LINE ('p')

// We make the addition and deletion characters unprintable so we are able to
// differentiate binary and textual proof files with the first character.
#define BINARY_ADDITION_LINE_START    (1)
#define BINARY_DELETION_LINE_START    (2)

#define READ_LONG_TOKEN(res, f, ptr)            do {                           \
    res = fscanf(f, "%lld ", ptr);                                             \
    PRINT_ERR_AND_EXIT_IF(res == 0, "Token was expected to be a number.");     \
    PRINT_ERR_AND_EXIT_IF(res == EOF, "EOF unexpectedly reached.");            \
    PRINT_ERR_AND_EXIT_IF(res < 0, "Other error encountered while parsing.");  \
  } while (0)

#define READ_INT_TOKEN(res, f, ptr)             do {                           \
    res = fscanf(f, "%d ", ptr);                                               \
    PRINT_ERR_AND_EXIT_IF(res == 0, "Token was expected to be a number.");     \
    PRINT_ERR_AND_EXIT_IF(res == EOF, "EOF unexpectedly reached.");            \
    PRINT_ERR_AND_EXIT_IF(res < 0, "Other error encountered while parsing.");  \
  } while (0)

// Reads a literal from `f`. Literals are assumed to always fit in an `int`.
#define READ_LIT            READ_INT_TOKEN

#ifdef LONGTYPE
// The kind of numeric token we read by default.
#define READ_CLAUSE_ID      READ_LONG_TOKEN

#define SRID_FORMAT_STR     ("%lld")

// Problem header format string for CNFs.
#define CNF_HEADER_STR      (" cnf %d %lld\n")
#else
// The kind of numeric token we read by default.
#define READ_CLAUSE_ID      READ_INT_TOKEN

#define SRID_FORMAT_STR     ("%d")

// Problem header format string for CNFs.
#define CNF_HEADER_STR      (" cnf %d %d\n")
#endif

////////////////////////////////////////////////////////////////////////////////

// A flag for whether the DSR/LSR proof file is in binary format.
// By default, assumes the proof is not in binary format.
extern int read_binary;

// A flag for whether the LSR proof file should be written in binary format.
// By default. assumes the proof should not be written in binary format.
extern int write_binary;

// Parses a literal in binary format. Called by `parse_lit`.
// Return value is in DIMACS format.
// Expects a literal to read. If EOF is reached, it prints an error and exits.
int read_lit_binary(FILE *f);

// Parses a lit from the provided file according to `read_binary`.
// Return value is in DIMACS format.
// Expects a literal to read. If EOF is reached, it prints an error and exits.
int read_lit(FILE *f);

// Writes a literal in DIMACS format to the file in binary format.
void write_lit_binary(FILE *f, int lit);

// Takes a lit in 0-indexed format and writes it to the file according to `write_binary`.
void write_lit(FILE *f, int lit);

// Parses a clause ID in binary format. Called by `parse_clause_id`.
// Return value is the uncompressed value.
// Expects a clause ID to read. If EOF is reached, it prints an error and exits.
srid_t read_clause_id_binary(FILE *f);

// Parses a clause ID from the provided file according to `read_binary`.
// Return value is the uncompressed value.
// Expects a clause ID to read. If EOF is reached, it prints an error and exits.
srid_t read_clause_id(FILE *f);

// Takes a clause ID in 1-indexed format and writes it to the file in binary format.
void write_clause_id_binary(FILE *f, srid_t clause_id);

// Takes a clause ID in 1-indexed format and writes it to the file according to `write_binary`.
void write_clause_id(FILE *f, srid_t clause_id);

int read_dsr_line_start(FILE *f);
int read_lsr_line_start(FILE *f, srid_t *line_id);

void write_dsr_line_start(FILE *f, int is_deletion_line);
void write_lsr_line_start(FILE *f, srid_t line_id, int is_deletion_line);

// Ends the line. Prints a 0 and a newline character, if applicable.
void write_sr_line_end(FILE *f);

// Determines if there is potentially another line in the FILE.
// If not binary, ignores whitespace until the start of the line is found.
// Returns 1 if another line could exist, and `f` points to the start of the line.
// Returns 0 if EOF encountered.
// Errors and exits if an unexpected character is found.
int has_another_line(FILE *f);

#endif /* _GLOBAL_PARSING_H_ */