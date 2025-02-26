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

void cli_init(cli_opts_t *cli) {
  memset(cli, 0, offsetof(cli_opts_t, cnf_file_path_buf));
  cli->cnf_file_path_buf[MAX_FILE_PATH_LEN - 1] = '\0';
  cli->dsr_file_path_buf[MAX_FILE_PATH_LEN - 1] = '\0';
  cli->lsr_file_path_buf[MAX_FILE_PATH_LEN - 1] = '\0';
}

static inline void err_if_option_already_set(int val, int optopt) {
  FATAL_ERR_IF(val, "Option \"-%c\" was already set.", (char) optopt);
}

static void copy_and_update_bufs(cli_opts_t *cli, size_t len) {
  cli->buf_offset = len;
  memcpy(cli->dsr_file_path_buf, cli->cnf_file_path_buf, len + 1);
  memcpy(cli->lsr_file_path_buf, cli->cnf_file_path_buf, len + 1);
  cli->dsr_file_path = ((char *) cli->dsr_file_path_buf) + len;
  cli->lsr_file_path = ((char *) cli->lsr_file_path_buf) + len;
}

// Handles the common CLI options.
cli_res_t cli_handle_opt(cli_opts_t *cli, int opt, int optopt, char *optarg) {
  switch (opt) {
  case HELP_MSG_OPT:
    return CLI_HELP_MESSAGE;
  case QUIET_MODE_OPT:
    err_if_option_already_set(cli->quiet_mode_set, optopt);
    FATAL_ERR_IF(cli->verbose_mode_set,
      "Cannot set both quiet and verbose modes.");
    verbosity_level = VL_QUIET;
    cli->quiet_mode_set = 1;
    break;
  case VERBOSE_MODE_OPT:
    err_if_option_already_set(cli->verbose_mode_set, optopt);
    FATAL_ERR_IF(cli->quiet_mode_set,
      "Cannot set both quiet and verbose modes.");
    verbosity_level = VL_VERBOSE;
    cli->verbose_mode_set = 1;
    break;
  case EAGER_OPT:
    err_if_option_already_set(cli->eager_strategy_set, optopt);
    FATAL_ERR_IF(cli->streaming_strategy_set,
      "Cannot set both eager and streaming parsing strategies.");
    p_strategy = PS_EAGER;
    cli->eager_strategy_set = 1;
    break;
  case STREAMING_OPT:
    err_if_option_already_set(cli->streaming_strategy_set, optopt);
    FATAL_ERR_IF(cli->eager_strategy_set,
      "Cannot set both eager and streaming parsing strategies.");
    p_strategy = PS_STREAMING;
    cli->streaming_strategy_set = 1;
    break;
  case DIR_OPT:
    err_if_option_already_set(cli->dir_provided, optopt);
    FATAL_ERR_IF(cli->name_provided,
      "Cannot provide both a name and a directory prefix.");
    cli->dir_provided = 1;

    int len = snprintf(cli->cnf_file_path_buf, MAX_FILE_PATH_LEN, "%s", optarg);
    FATAL_ERR_IF(len >= MAX_FILE_PATH_LEN,
      "Directory prefix too long.");
    FATAL_ERR_IF(len == 0, "Empty directory provided.");
    cli->cnf_file_path = ((char *) cli->cnf_file_path_buf) + len;

    // Add an ending directory '/' if one was omitted
    if (cli->cnf_file_path[-1] != '/') {
      memcpy(cli->cnf_file_path++, "/", 2);
      len++;
    }

    copy_and_update_bufs(cli, len);
    break;
  case NAME_OPT:
    err_if_option_already_set(cli->name_provided, optopt);
    FATAL_ERR_IF(cli->dir_provided,
      "Cannot provide both a name and a directory prefix.");
    cli->name_provided = 1;
    
    len = snprintf(cli->cnf_file_path_buf, MAX_FILE_PATH_LEN, "%s", optarg);
    FATAL_ERR_IF(len >= MAX_FILE_PATH_LEN, "Name prefix too long.");
    cli->cnf_file_path = ((char *) cli->cnf_file_path_buf) + len;
    copy_and_update_bufs(cli, len);
    break;
  case '?':
    log_err("Unknown option provided.");
    return CLI_HELP_MESSAGE;
  case ':':
    log_err("Argument missing for option \"-%c\".", (char) optopt);
    return CLI_HELP_MESSAGE;
  default:
    return CLI_UNRECOGNIZED;
  }

  return CLI_SUCCESS;
}

// Concatenates the file extensions to the middle of the buffers,
// then sets the file path pointers back to the start of the buffers.
void cli_concat_path_extensions(cli_opts_t *cli,
                                char *cnf_ext, char *dsr_ext, char *lsr_ext) {
  // We subtract 2 off the MAX_LEN to prevent buffer overflow,
  // making use of the nul-terminator in the last index
  memcpy(cli->cnf_file_path, cnf_ext,
    1 + strnlen(cnf_ext, (MAX_FILE_PATH_LEN - 2) - cli->buf_offset));
  memcpy(cli->dsr_file_path, dsr_ext,
    1 + strnlen(dsr_ext, (MAX_FILE_PATH_LEN - 2) - cli->buf_offset));
  memcpy(cli->lsr_file_path, lsr_ext,
    1 + strnlen(lsr_ext, (MAX_FILE_PATH_LEN - 2) - cli->buf_offset));
  cli->cnf_file_path = cli->cnf_file_path_buf;
  cli->dsr_file_path = cli->dsr_file_path_buf;
  cli->lsr_file_path = cli->lsr_file_path_buf;
}