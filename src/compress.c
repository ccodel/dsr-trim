/**
 * @file compress.c
 * @brief A tool to compress and decompress DSR and LSR proof files.
 * 
 * Through the magic of encapsulation and API design, the code paths
 * to compress and decompress proofs are exactly the same, modulo setting
 * the `read_binary` and `write_binary` flags in `global_parsing.c`.
 * Since we can detect if an input proof is either DSR/LSR and either
 * binary/human-readable, we can use this tool to convert between
 * compressed and decompressed proofs automatically, without the need
 * for user-supplied command-line flags.
 * 
 * In other words, don't let the names `compress_Xsr_proof()` fool you:
 * they handle both compression and decompression.
 * 
 * Compression takes ASCII numerical tokens (e.g. `144`, or `-23`)
 * and converts them into a variable-length binary format, where the
 * most-significant bit of each byte indicates if there are more bytes
 * in the number. See `write_lit_binary()` and `write_clause_id_binary()`
 * in `global_parsing.c` for more details.
 * 
 * @todo Allow `input_file` to be `stdin`. Right now, we assume it's a file,
 *       so that we may `rewind()` after detecting if the proof is DSR or LSR.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-04-02
 */

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>    // isspace()
#include <getopt.h>   // getopt_long()

#include "xio.h"
#include "global_data.h"
#include "global_parsing.h"
#include "logger.h"

////////////////////////////////////////////////////////////////////////////////

#define ZEROS_IN_LSR_ADDITION_LINE    (2)
#define ZEROS_IN_LSR_DELETION_LINE    (1)

static FILE *input_file;
static FILE *output_file;

////////////////////////////////////////////////////////////////////////////////

#define HELP_OPT      ('h')
#define OPT_STR       ("h")

static struct option const longopts[] = {
  { "help", no_argument, NULL, HELP_OPT },
  { NULL, 0, NULL, 0 }
};

static void print_usage(FILE *f) {
  fprintf(f, "Usage: ./compress <input_file> [output_file]\n");
  fprintf(f, "\n");
  fprintf(f, "A tool to compress and decompress DSR and LSR proofs.\n");
  fprintf(f, "(De)compression is determined by the input file's format.\n");
  fprintf(f, "\n");
  fprintf(f, "Alternatively, you can add these options:\n");
  fprintf(f, "\n");
  fprintf(f, "  -h | --help    Prints this help message and exits.\n");
  fprintf(f, "\n");
  fprintf(f, "When an output file is not provided, `stdout` is used.\n");
  fprintf(f, "Compressed proofs aren't human-readable, so we recommend\n");
  fprintf(f, "using pipes/redirection when using `stdout` for compression.\n");
  fprintf(f, "\n");
}

// Returns `1` if the proof is a compressed DSR proof, `0` if compressed LSR.
static int is_compressed_dsr_proof(void) {
  // Determine if the first character indicates DSR or LSR
  int c = getc_unlocked(input_file);
  ungetc(c, input_file);
  switch (c) {
    case DSR_BINARY_ADDITION_LINE_START:
    case DSR_BINARY_DELETION_LINE_START:
      return 1;
    case LSR_BINARY_ADDITION_LINE_START:
    case LSR_BINARY_DELETION_LINE_START:
      return 0;
    default:
      log_fatal_err("Unexpected first character in proof file: %c (%d).", c, c);
      return -1; // unreachable
  }
}

/**
 * @brief Determines if the `input_file` is a DSR proof or an LSR proof.
 * 
 * The compressed case is easy: check the first character.
 * See `is_compressed_dsr_proof()`.
 * 
 * In the human-readable case, we need to parse an entire proof line.
 * The cases are as follows:
 * 
 * - DSR deletion: it starts with a 'd' character.
 * - DSR addition: it has one '0'.
 * - LSR deletion: its second token is a 'd' character.
 * - LSR addition: it has two '0's.
 * 
 * Since we will be consuming the line, we call `rewind()` before we
 * return from this function to reset the `input_file` stream.
 * 
 * @return `1` if is DSR, `0` if LSR.
 */
static int is_dsr_proof(void) {
  if (!has_another_line(input_file)) {
    log_fatal_err("The proof file was empty.");
  }

  if (read_binary) {
    return is_compressed_dsr_proof();
  }

  // See if the first line is DSR deletion (i.e., the first character is 'd')
  int is_dsr;
  if (scan_until_char(input_file, 'd')) {
    is_dsr = 1;
    goto rewind_and_return;
  } 

  // Not a DSR deletion line, so the line must start with a clause ID/literal
  srid_t clause_id = read_clause_id(input_file);

  // Could this be a DSR addition line?
  // The shortest possible proof line is the DSR addition of the empty clause
  // Since LSR lines can't start with '0', a `clause_id` of 0 means DSR add
  if (clause_id == 0) {
    is_dsr = 1;
    goto rewind_and_return;
  }

  // Otherwise, check if the line is LSR deletion (i.e. the next token is 'd')
  if (scan_until_char(input_file, 'd')) {
    is_dsr = 0;
    goto rewind_and_return;
  }
    
  /* 
   * This line is not a deletion line, whether DSR or LSR.
   * It must be an addition line, but of which type?
   * To figure that out, we scan the whole line and count the number of 0s.
   *
   * ASSUMPTION: The first proof line fits on exactly one line.
   * Currently, dsr-trim only generates LSR proofs with one line per proof line.
   * However, the input proof might not follow this convention.
   * If the first proof line spans multiple lines, we have unexpected behavior.
   */
  int num_zeros_found = 0;
  int c;
  while ((c = getc_unlocked(input_file)) != EOF) {
    if (c == '\n')  break;    // Stop when we reach the end of the line
    if (isspace(c)) continue; // Consume non-newline whitespace
    ungetc(c, input_file);    // Restore the non-whitespace character

    srid_t token = read_clause_id(input_file);
    num_zeros_found += (token == 0);
  }

  switch (num_zeros_found) {
    case 1: is_dsr = 1; break;
    case 2: is_dsr = 0; break;
    default:
      log_fatal_err("Unexpected number of 0s (%d) found in first proof line.",
        num_zeros_found);
  }

  // Reset `input_file` back to the start of the file
  rewind_and_return:
  rewind(input_file); 
  return is_dsr;
}

/**
 * @brief (De)compresses the DSR proof from `input_file` into `output_file`.
 * 
 * We read and write a token at a time and mark when lines start and end.
 * Reading and writing happens in the correct formats due to setting the
 * `read_binary` and `write_binary` flags in `main()`.
 */
static void compress_dsr_proof(void) {
  srid_t token;
  while (has_another_line(input_file)) {
    int line_type = read_dsr_line_start(input_file);
    if (line_type == ADDITION_LINE) {
      write_dsr_addition_line_start(output_file);
    } else {
      write_dsr_deletion_line_start(output_file);
    }

    // Keep reading tokens until the line-ending 0 is read (but don't print it)
    while ((token = read_clause_id(input_file)) != 0) {
      write_clause_id(output_file, token);
    }

    // The 0 gets printed here (but we encapsulate it)
    write_sr_line_end(output_file);
  }
}

/**
 * @brief (De)compresses the LSR proof from `input_file` into `output_file`.
 * 
 * We read and write a token at a time and mark when lines start and end.
 * See `compress_dsr_proof()` for more notes.
 */
static void compress_lsr_proof(void) {
  srid_t token, line_id;
  while (has_another_line(input_file)) {
    int line_type = read_lsr_line_start(input_file, &line_id);
    FATAL_ERR_IF(line_id <= 0, "Line id (%lld) was non-positive.", line_id);

    int zeros_left;
    if (line_type == ADDITION_LINE) {
      write_lsr_addition_line_start(output_file, line_id);
      zeros_left = ZEROS_IN_LSR_ADDITION_LINE;
    } else {
      write_lsr_deletion_line_start(output_file, line_id);
      zeros_left = ZEROS_IN_LSR_DELETION_LINE;
    }
    
    // Keep reading tokens until enough zeros for the line type are read
    while (zeros_left > 0) {
      // The first chunk of tokens in an addition lines are literals
      if (zeros_left == ZEROS_IN_LSR_ADDITION_LINE) {
        token = read_lit(input_file);
        write_lit(output_file, token);
      } else {
        token = read_clause_id(input_file);
        if (token != 0) {
          write_clause_id(output_file, token);
        }
      }

      zeros_left -= (token == 0);
    }

    write_sr_line_end(output_file);
  }
}

int main(int argc, char *argv[]) {
  // Print a help message, and return an error code if too many arguments
  if (argc <= 1 || argc > 3) {
    print_usage((argc == 1) ? stdout : stderr);
    return (argc != 1);
  }

  // Process any command-line options
  int ch;
  while ((ch = getopt_long(argc, argv, OPT_STR, longopts, NULL)) != -1) {
    switch (ch) {
      case HELP_OPT:
        print_usage(stdout);
        return 0;
      default:
        log_err("Unknown option: %c", ch);
        print_usage(stderr);
        return 1;
    }
  }

  // Open the proof file(s)
  // Note: `getopt_long()` shifts non-option arguments to the end of `argv`
  output_file = stdout;
  switch (argc - optind) {
    case 2:
      output_file = xfopen(argv[optind + 1], "w");
      // Fallthrough
    case 1:
      input_file = xfopen(argv[optind], "r");
      break;
    default:
      print_usage(stderr);
      return 1;
  }

  // Write the opposite format of what we detect we will be reading
  configure_proof_file_parsing(input_file);
  write_binary = !read_binary;
  
  int is_dsr = is_dsr_proof();
  if (is_dsr) {
    compress_dsr_proof();
  } else {
    compress_lsr_proof();
  }

  return 0;
}
