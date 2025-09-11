/**
 * @file global_parsing.c
 * @brief A collection of common parsing functions for DIMACS CNf/DSR/LSR files.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-04-02
 */

#include <ctype.h>

#include "global_data.h"
#include "global_parsing.h"
#include "logger.h"

////////////////////////////////////////////////////////////////////////////////

int read_binary = 0;
int write_binary = 0;

int configure_proof_file_parsing(FILE *f) {
  int c = getc_unlocked(f);
  ungetc(c, f);
  read_binary = IS_BINARY_LINE_START(c);
  return read_binary;
}

/**
 * @brief Scans the file `f` until a matching character `match` is found.
 *        
 * Any intervening whitespace is consumed.
 * If `match` is found, then the `match` character is consumed from `f`.
 * 
 * Errors and exits if EOF is encountered before `match` is found.
 * 
 * @param f The file stream to read characters from.
 * @param match The character to search for. Cannot be a whitespace character.
 * @return 1 if `match` was found and consumed, 0 otherwise.
 */
int scan_until_char(FILE *f, int match) {
  int c;
  while ((c = getc_unlocked(f)) != EOF) {
    if (c == match) {
      return 1;
    } else if (!isspace(c)) {
      ungetc(c, f);
      return 0;
    }
  }

  log_fatal_err("EOF while scanning for character.");
  return EOF;
}

int read_lit_binary(FILE *f) {
  int x = 0;
  int new_lsb, shift = 0;
  do {
    new_lsb = getc_unlocked(f);
    FATAL_ERR_IF(new_lsb == EOF, "EOF while parsing binary lit.");

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

int read_formula_lit(FILE *f) {
  // Ignore all upcoming comment lines
  while (scan_until_char(f, '\n')) {
    int c = getc_unlocked(f);
    if (c == DIMACS_COMMENT_LINE) {
      // Read to the end of the line, discarding the comment
      while (getc_unlocked(f) != '\n') {}
      ungetc('\n', f); // Invariant: leave newlines unconsumed
    } else {
      ungetc(c, f);
      break;
    }
  }
  
  int res, lit;
  READ_LIT(res, f, &lit);
  return lit;
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

/**
 * @brief Throws a fatal error that the file `f` is not a binary proof file.
 * 
 * Rather than throw a blanket "unexpected character" error when trying to
 * parse a binary proof file, we instead examine `f` to see if it is an
 * uncompressed proof file or if we encountered a truly unexpected
 * character. This function prints the appropriate error message.
 * 
 * @param f The proof file that was expected to contain a binary proof.
 */
static void err_not_binary_proof(FILE *f) {
  // If `f` starts with human-readable proof characters,
  // then `f` might contain an uncompressed DSR/LSR proof
  int c;
  while ((c = getc_unlocked(f)) != EOF) {
    if (isspace(c)) {
      continue;
    } else if (IS_HUMAN_READABLE_PROOF_CHAR(c)) {
      log_fatal_err("Expected a binary proof, got an uncompressed proof.");
    } else {
      log_fatal_err("Unexpected character encountered: %c.", c);
    }
  }
  
  log_fatal_err("The proof file was empty or contained only whitespace.");
}

line_type_t read_dsr_line_start(FILE *f) {
  if (read_binary) {
    // The next character should be the binary version of 'a' or 'd'
    int c = getc_unlocked(f);
    switch (c) {
      case DSR_BINARY_ADDITION_LINE_START: return ADDITION_LINE;
      case DSR_BINARY_DELETION_LINE_START: return DELETION_LINE;
      case LSR_BINARY_ADDITION_LINE_START:
      case LSR_BINARY_DELETION_LINE_START:
        log_fatal_err("Expected a binary DSR proof, got an LSR proof instead.");
      default:
        err_not_binary_proof(f);
    }
  } else {
    if (scan_until_char(f, 'd')) {
      // We found a deletion line!
      // Check that the next character is whitespace (and consume it)
      int c = getc_unlocked(f);
      FATAL_ERR_IF(!isspace(c), "Expected whitespace after 'd'.");
      return DELETION_LINE;
    }
  }

  return ADDITION_LINE;
}

line_type_t read_lsr_line_start(FILE *f, srid_t *line_id) {
  if (read_binary) {
    // Consume the BINARY start character, and then the clause ID
    int c = getc_unlocked(f);
    line_type_t line_type;
    switch (c) {
      case DSR_BINARY_ADDITION_LINE_START:
      case DSR_BINARY_DELETION_LINE_START:
        log_fatal_err("Expected a binary LSR proof, got a DSR proof instead.");
      case LSR_BINARY_ADDITION_LINE_START: line_type = ADDITION_LINE; break;
      case LSR_BINARY_DELETION_LINE_START: line_type = DELETION_LINE; break;
      default:
        err_not_binary_proof(f);
    }
    
    *line_id = read_clause_id_binary(f);
    return line_type;
  } else {
    // Scan the line ID first, and then check for a deletion line.
    int res;
    READ_CLAUSE_ID(res, f, line_id);
    FATAL_ERR_IF(*line_id <= 0, "Line ID is not positive");
    return read_dsr_line_start(f);
  }
}

void write_dsr_addition_line_start(FILE *f) {
  if (write_binary) {
    putc_unlocked(DSR_BINARY_ADDITION_LINE_START, f);
  }
}

void write_dsr_deletion_line_start(FILE *f) {
  if (write_binary) {
    putc_unlocked(DSR_BINARY_DELETION_LINE_START, f);
  } else {
    putc_unlocked('d', f);
    putc_unlocked(' ', f);
  }
}
void write_lsr_addition_line_start(FILE *f, srid_t line_id) {
  if (write_binary) {
    putc_unlocked(LSR_BINARY_ADDITION_LINE_START, f);
    write_clause_id_binary(f, line_id);
  } else {
    write_clause_id(f, line_id);
  }
}

void write_lsr_deletion_line_start(FILE *f, srid_t line_id) {
  if (write_binary) {
    putc_unlocked(LSR_BINARY_DELETION_LINE_START, f);
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
    int c = getc_unlocked(f);
    if (c == EOF) {
      return 0;
    } else if (IS_BINARY_LINE_START(c)) {
      ungetc(c, f);
      return 1;
    } else {
      log_fatal_err("Unexpected binary character found: %c.", c);
    }
  } else {
    // Ignore whitespace until a digit is found. Error if non-digit found.
    while ((c = getc_unlocked(f)) != EOF) {
      if (!isspace(c)) {
        if (IS_HUMAN_READABLE_PROOF_CHAR(c)) {
          ungetc(c, f);
          return 1;
        } else {
          log_fatal_err("Found a non-digit at start of line.");
        }
      }
    }
  }

  return 0;
}