/**
 * @file cli.c
 * @brief Common command line options and parsing utilities.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-10
 */

#include <stdio.h>
#include <string.h>

#include "cli.h"
#include "global_types.h"
#include "global_parsing.h"
#include "logger.h"

////////////////////////////////////////////////////////////////////////////////

#define HELP_MSG_OFFSET         (0)
#define QUIET_VERBOSE_OFFSET    (1)
#define VERBOSE_ERRORS_OFFSET   (2)
#define DIR_OFFSET              (3)
#define NAME_OFFSET             (4)
#define EAGER_STREAMING_OFFSET  (5)

#define HELP_MSG_MASK         (1 << HELP_MSG_OFFSET)
#define QUIET_VERBOSE_MASK    (1 << QUIET_VERBOSE_OFFSET)
#define VERBOSE_ERRORS_MASK   (1 << VERBOSE_ERRORS_OFFSET)
#define DIR_MASK              (1 << DIR_OFFSET)
#define NAME_MASK             (1 << NAME_OFFSET)
#define EAGER_STREAMING_MASK  (1 << EAGER_STREAMING_OFFSET)

void cli_init(cli_opts_t *cli) {
  memset(cli, 0, offsetof(cli_opts_t, cnf_file_path_buf));
  cli->cnf_file_path_buf[MAX_FILE_PATH_LEN - 1] = '\0';
  cli->dsr_file_path_buf[MAX_FILE_PATH_LEN - 1] = '\0';
  cli->lsr_file_path_buf[MAX_FILE_PATH_LEN - 1] = '\0';
}

static int cli_is_name_opt_set(cli_opts_t *cli) {
  return cli->opt_set_flags & NAME_MASK;
}

static int cli_is_dir_opt_set(cli_opts_t *cli) {
  return cli->opt_set_flags & DIR_MASK;
}

// Returns the bitmask for the option.
// Returns -1 if the option isn't known (which is possible, since callers
// may wish to handle their own options).
static int get_mask_from_opt(int opt) { 
  switch (opt) {
    case HELP_MSG_OPT: // waterfall
    case LONG_HELP_MSG_OPT: return HELP_MSG_MASK;
    case QUIET_MODE_OPT: // waterfall
    case VERBOSE_MODE_OPT: return QUIET_VERBOSE_MASK;
    case VERBOSE_ERRORS_OPT: return VERBOSE_ERRORS_MASK;
    case DIR_OPT: return DIR_MASK;
    case NAME_OPT: return NAME_MASK;
    case EAGER_OPT: // waterfall
    case STREAMING_OPT: return EAGER_STREAMING_MASK;
    default: return -1;
  }
}

static void set_opt_flag_or_err_if_already_set(cli_opts_t *cli, int opt) {
  int mask = get_mask_from_opt(opt);
  if (mask >= 0) {
    FATAL_ERR_IF(cli->opt_set_flags & mask,
    "Option \"-%c\" (or, maybe, its opposite) was already given.", (char) opt);

    // Special case: NAME and DIR, since we need to track each one separately
    FATAL_ERR_IF((opt == NAME_OPT && cli_is_dir_opt_set(cli))
      || (opt == DIR_OPT && cli_is_name_opt_set(cli)),
      "Cannot provide both a directory and a name prefix.");
    
    cli->opt_set_flags |= mask;
  }
}

static void copy_and_update_bufs(cli_opts_t *cli, size_t len) {
  cli->buf_offset = len;
  memcpy(cli->dsr_file_path_buf, cli->cnf_file_path_buf, len + 1);
  memcpy(cli->lsr_file_path_buf, cli->cnf_file_path_buf, len + 1);
  cli->dsr_file_path = ((char *) cli->dsr_file_path_buf) + len;
  cli->lsr_file_path = ((char *) cli->lsr_file_path_buf) + len;
}

// Handles the common CLI options.
cli_res_t cli_handle_opt(cli_opts_t *cli, int opt, int optopt,
                         char *optstr, char *optarg) {
  set_opt_flag_or_err_if_already_set(cli, opt);
  int len; // Used for string options

  // Now actually process the option
  switch (opt) {
  case HELP_MSG_OPT:        return CLI_HELP_MESSAGE;
  case LONG_HELP_MSG_OPT:   return CLI_LONG_HELP_MESSAGE;
  case QUIET_MODE_OPT:      verbosity_level = VL_QUIET; break;
  case VERBOSE_MODE_OPT:
    verbosity_level = VL_VERBOSE;
    err_verbosity_level = VL_NORMAL;
    break;
  case VERBOSE_ERRORS_OPT:  err_verbosity_level = VL_VERBOSE; break;
  case EAGER_OPT:           p_strategy = PS_EAGER; break;
  case STREAMING_OPT:       p_strategy = PS_STREAMING; break;
  case DIR_OPT:
    len = snprintf(cli->cnf_file_path_buf, MAX_FILE_PATH_LEN, "%s", optarg);
    FATAL_ERR_IF(len >= MAX_FILE_PATH_LEN, "Directory prefix too long.");
    FATAL_ERR_IF(len == 0, "Empty directory string provided.");
    cli->cnf_file_path = ((char *) cli->cnf_file_path_buf) + len;

    // Add an ending directory '/' if one was omitted
    if (cli->cnf_file_path[-1] != '/') {
      memcpy(cli->cnf_file_path++, "/", 2);
      len++;
    }

    copy_and_update_bufs(cli, len);
    break;
  case NAME_OPT:
    len = snprintf(cli->cnf_file_path_buf, MAX_FILE_PATH_LEN, "%s", optarg);
    FATAL_ERR_IF(len >= MAX_FILE_PATH_LEN, "Name prefix too long.");
    FATAL_ERR_IF(len == 0, "Empty name prefix string provided.");
    cli->cnf_file_path = ((char *) cli->cnf_file_path_buf) + len;
    copy_and_update_bufs(cli, len);
    break;
  case '?':
    return CLI_HELP_MESSAGE_TO_STDERR;
  default:
    return CLI_UNRECOGNIZED;
  }

  return CLI_SUCCESS;
}

// Concatenates the file extensions to the middle of the buffers,
// then sets the file path pointers back to the start of the buffers.
static void cli_concat_paths(cli_opts_t *cli, char *cnf, char *dsr, char *lsr) {
  // We subtract 2 off the MAX_LEN to prevent buffer overflow,
  // making use of the nul-terminator in the last index
  memcpy(cli->cnf_file_path, cnf,
    1 + strnlen(cnf, (MAX_FILE_PATH_LEN - 2) - cli->buf_offset));
  cli->cnf_file_path = cli->cnf_file_path_buf;

  if (dsr != NULL) {
    memcpy(cli->dsr_file_path, dsr,
      1 + strnlen(dsr, (MAX_FILE_PATH_LEN - 2) - cli->buf_offset));
    cli->dsr_file_path = cli->dsr_file_path_buf;
  } else {
    cli->dsr_file_path = NULL;
  }

  if (lsr != NULL) {
    memcpy(cli->lsr_file_path, lsr,
      1 + strnlen(lsr, (MAX_FILE_PATH_LEN - 2) - cli->buf_offset));
    cli->lsr_file_path = cli->lsr_file_path_buf;
  } else {
    cli->lsr_file_path = NULL;
  }
}

// The only way to provide 0 file arguments is if `-n` is provided.
// In that case, take the base name (i.e. the argument to `-n`)
// and append the expected file extensions.
// Otherwise, print an error.
static cli_res_t cli_bad_dir_opt_err(int is_dsr_trim, int num_provided_args) {
  if (is_dsr_trim) {
    log_err("Cannot provide a directory without a formula file name.");
  } else {
    log_err("Cannot provide a directory without both formula and LSR file names.");
  }

  return CLI_HELP_MESSAGE_TO_STDERR;
}

static cli_res_t cli_parse_file_paths(
      cli_opts_t *cli, char *argv[], int argc, int optind, int is_dsr_trim) {
  char *cnf = NULL, *dsr = NULL, *lsr = NULL;
  switch (argc - optind) {
  case 0:
    if (cli_is_dir_opt_set(cli)) {
      return cli_bad_dir_opt_err(is_dsr_trim, argc - optind);
    } else if (cli_is_name_opt_set(cli)) {
      cnf = ".cnf";
      dsr = (is_dsr_trim) ? ".sr" : NULL;
      lsr = ".lsr";
    } else {
      // Emit an error for not providing input file names
      if (is_dsr_trim) {
        log_err("No CNF, DSR, or LSR file names provided.");
      } else {
        log_err("No CNF or LSR file names provided.");
      }
      return CLI_HELP_MESSAGE_TO_STDERR;
    }
    break;
  case 1:
    if (cli_is_dir_opt_set(cli)) {
      return cli_bad_dir_opt_err(is_dsr_trim, argc - optind);
    } else if (cli_is_name_opt_set(cli)) {
      // The input is the extension for the "base" proof file
      cnf = ".cnf";
      dsr = (is_dsr_trim) ? argv[optind] : NULL;
      lsr = (is_dsr_trim) ? ".lsr" : argv[optind];
    } else {
      // Without `-n` or `-d`, the input is the CNF file
      cnf = argv[optind];
    }
    break;
  case 2:
    if (cli_is_dir_opt_set(cli)) {
      // The two inputs are the CNF and "base" proof file
      cnf = argv[optind];
      dsr = (is_dsr_trim) ? argv[optind + 1] : NULL;
      lsr = (is_dsr_trim) ? NULL : argv[optind + 1];
    } else if (cli_is_name_opt_set(cli)) {
      // In `dsr-trim`, the inputs are the extensions for the proof files
      // In `lsr-check`, the inputs are the CNF and LSR files
      cnf = (is_dsr_trim) ? ".cnf" : argv[optind];
      dsr = (is_dsr_trim) ? argv[optind] : NULL;
      lsr = argv[optind + 1];
    } else {
      // Without `-n` or `-d`, the inputs are the CNF and one of the proofs
      cnf = argv[optind];
      dsr = (is_dsr_trim) ? argv[optind + 1] : NULL;
      lsr = (is_dsr_trim) ? NULL : argv[optind + 1];
    }
    break;
  case 3:
    // Fall through to default case if not dsr-trim
    if (is_dsr_trim) {
      // The inputs are the CNF, DSR, and LSR files
      cnf = argv[optind];
      dsr = argv[optind + 1];
      lsr = argv[optind + 2];
      break;
    } 
  default:
    log_err("Too many file arguments provided. Expected %d, got %d.",
        2 + is_dsr_trim, argc - optind);
    return CLI_HELP_MESSAGE_TO_STDERR;
  }

  if (cli_is_dir_opt_set(cli) || cli_is_name_opt_set(cli)) {
    cli_concat_paths(cli, cnf, dsr, lsr);
  } else {
    cli->cnf_file_path = cnf;
    cli->dsr_file_path = dsr;
    cli->lsr_file_path = lsr;
  }

  return CLI_SUCCESS;
}

cli_res_t cli_parse_file_paths_for_dsr_trim(
    cli_opts_t *cli, char *argv[], int argc, int optind) {
  return cli_parse_file_paths(cli, argv, argc, optind, 1);
}

cli_res_t cli_parse_file_paths_for_lsr_check(
    cli_opts_t *cli, char *argv[], int argc, int optind) {
  return cli_parse_file_paths(cli, argv, argc, optind, 0);
}
