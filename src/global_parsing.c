/**
 * @file global_parsing.c
 * @brief A collection of common parsing functions for DIMACS CNf/DSR/LSR files.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-04-02
 */

#include "global_data.h"
#include "global_parsing.h"

#include <stdio.h>
#include <ctype.h>

int read_binary = 0;
int write_binary = 0;

int read_lit_binary(FILE *f) {
  int x = 0;
  int new_lsb, shift = 0;
  do {
    new_lsb = getc_unlocked(f);
    PRINT_ERR_AND_EXIT_IF(new_lsb == EOF, "EOF while parsing binary lit.");

    x |= (new_lsb & 0x7f) << shift;
    shift += 7;
  } while (new_lsb > 0x7f);

  // Undo the binary encoding: divide by two, then correct sign
  if (x % 2) {
    return (x >> 1) * -1;
  } else {
    return x >> 1;
  }
}

int read_lit(FILE *f) {
  if (read_binary) {
    return read_lit_binary(f);
  } else {
    int res, lit;
    READ_LIT(res, f, &lit);
    return lit;
  }
}

void write_lit_binary(FILE *f, int lit) {
  unsigned int x = abs(lit) << 1;
  if (lit < 0) {
    x |= 0x1;
  }
  
  // Write 7-bit words at a time until all bits are written.
  do {
    if (x <= 0x7f) {
      putc_unlocked(x, f);
    } else {
      // The byte 0x80 sets the MSB of a byte.
      putc_unlocked(0x80 | (x & 0x7f), f);
    }

    x >>= 7;
  } while (x);
}

void write_lit(FILE *f, int lit) {
  if (write_binary) {
    write_lit_binary(f, lit);
  } else {
    fprintf(f, "%d ", lit);
  }
}

#ifdef LONGTYPE
srid_t read_clause_id_binary(FILE *f) {
  srid_t x = 0;
  int new_lsb, shift = 0;
  do {
    new_lsb = getc_unlocked(f);
    if (shift == 0 && new_lsb == EOF) {
      return EOF;
    }

    x |= ((srid_t) (new_lsb & 0x7f)) << shift;
    shift += 7;
  } while (new_lsb > 0x7f);

  // Undo the binary encoding: divide by two, then correct sign
  if (x % 2) {
    return (x >> 1) * -1;
  } else {
    return x >> 1;
  }
}

srid_t read_clause_id(FILE *f) {
  if (read_binary) {
    return read_clause_id_binary(f);
  } else {
    int res;
    srid_t clause_id;
    READ_CLAUSE_ID(res, f, &clause_id);
    return clause_id;
  }
}

void write_clause_id_binary(FILE *f, srid_t clause_id) {
  ullong x = llabs(clause_id) << 1;
  if (clause_id < 0) {
    x |= 0x1;
  }
  
  do {
    if (x <= 0x7f) {
      putc_unlocked(x, f);
    } else {
      // The byte 0x80 sets the MSB of a byte.
      putc_unlocked(0x80 | (x & 0x7f), f);
    }

    x >>= 7;
  } while (x);
}

void write_clause_id(FILE *f, srid_t clause_id) {
  if (write_binary) {
    write_clause_id_binary(f, clause_id);
  } else {
    fprintf(f, SRID_FORMAT_STR, clause_id);
    putc_unlocked(' ', f);
  }
}
#else
srid_t read_clause_id_binary(FILE *f) {
  return read_lit_binary(f);
}

srid_t read_clause_id(FILE *f) {
  return read_lit(f);
}

void write_clause_id_binary(FILE *f, srid_t clause_id) {
  write_lit_binary(f, clause_id);
}

void write_clause_id(FILE *f, srid_t clause_id) {
  write_lit(f, clause_id);
}
#endif

// Scans the input stream until a matching character is found. Ignores whitespace.
// Returns 1 if the character was found, and 0 if a non-matching, non-whitespace character was found.
// Errors and exits if EOF encountered.
static inline int scan_until_char(FILE *f, int match) {
  int c;
  while ((c = getc_unlocked(f)) != EOF) {
    if (c == match) {
      return 1;
    } else if (!isspace(c)) {
      ungetc(c, f);
      return 0;
    }
  }

  PRINT_ERR_AND_EXIT("EOF while scanning for character.");
}

line_type_t read_dsr_line_start(FILE *f) {
  if (read_binary) {
    // The next character should be 'a' or 'd'
    int c = getc_unlocked(f);
    switch (c) {
      case BINARY_ADDITION_LINE_START: return ADDITION_LINE;
      case BINARY_DELETION_LINE_START: return DELETION_LINE;
      default: PRINT_ERR_AND_EXIT("Line didn't start with a good character.");
    }
  } else {
    if (scan_until_char(f, 'd')) {
      // Check that the next character is whitespace
      int c = getc_unlocked(f);
      PRINT_ERR_AND_EXIT_IF(!isspace(c), "Expected whitespace after 'd'.");
      return DELETION_LINE;
    }
  }

  return ADDITION_LINE;
}

line_type_t read_lsr_line_start(FILE *f, srid_t *line_id) {
  if (read_binary) {
    // Scan for addition/deletion line, then a clause id
    int res = read_dsr_line_start(f);
    *line_id = read_clause_id_binary(f);
    return res;
  } else {
    // Scan the line ID first, and then check for a deletion line.
    int res;
    READ_CLAUSE_ID(res, f, line_id);
    PRINT_ERR_AND_EXIT_IF(*line_id <= 0, "Line ID is not positive");
    return read_dsr_line_start(f);
  }
}

void write_dsr_addition_line_start(FILE *f) {
  if (write_binary) {
    putc_unlocked(BINARY_ADDITION_LINE_START, f);
  }
}

void write_dsr_deletion_line_start(FILE *f) {
  if (write_binary) {
    putc_unlocked(BINARY_DELETION_LINE_START, f);
  } else {
    putc_unlocked('d', f);
    putc_unlocked(' ', f);
  }
}
void write_lsr_addition_line_start(FILE *f, srid_t line_id) {
  if (write_binary) {
    putc_unlocked(BINARY_ADDITION_LINE_START, f);
    write_clause_id_binary(f, line_id);
  } else {
    write_clause_id(f, line_id);
  }
}

void write_lsr_deletion_line_start(FILE *f, srid_t line_id) {
  if (write_binary) {
    putc_unlocked(BINARY_DELETION_LINE_START, f);
    write_clause_id_binary(f, line_id);
  } else {
    write_clause_id(f, line_id);
    putc_unlocked('d', f);
    putc_unlocked(' ', f);
  }
}

void write_sr_line_end(FILE *f) {
  if (write_binary) {
    write_lit_binary(f, 0);
  } else {
    putc_unlocked('0', f);
    putc_unlocked('\n', f);
  }
}

int has_another_line(FILE *f) {
  int c;
  if (read_binary) {
    // Should find either 'a' or 'd'
    switch ((c = getc_unlocked(f))) {
      case BINARY_ADDITION_LINE_START:
      case BINARY_DELETION_LINE_START:
        ungetc(c, f);
        return 1;
      case EOF: return 0;
      default:  PRINT_ERR_AND_EXIT("Unexpected binary character found.");
    }
  } else {
    // Ignore whitespace until a digit is found. Error if non-digit found.
    while ((c = getc_unlocked(f)) != EOF) {
      if (!isspace(c)) {
        if (isdigit(c) || c == '-' || c == 'd') {
          ungetc(c, f);
          return 1;
        } else {
          PRINT_ERR_AND_EXIT("Found a non-digit at start of line.");
        }
      }
    }
  }

  return 0;
}