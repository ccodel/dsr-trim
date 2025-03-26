/**
 * @file cli.h
 * @brief Common command line options and parsing utilities.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-10
 */

#ifndef _DSR_TRIM_CLI_H_
#define _DSR_TRIM_CLI_H_

#include <stddef.h>

/**
 * @brief The maximum length a file string have during CLI parsing.
 * 
 * The `dsr-trim` and `lsr-check` tools both provide a `--dir` option to
 * help minimize the amount of typing to specify the file paths to CNF and
 * proof files in the same or similar directories. However, this means that
 * the directory and file strings are separate, and so to cap the length of
 * a string buffer, we use this macro.
 */
#define MAX_FILE_PATH_LEN       (256)

#define HELP_MSG_OPT            ('h')
#define QUIET_MODE_OPT          ('q')
#define VERBOSE_MODE_OPT        ('v')
#define VERBOSE_ERRORS_OPT      ('V')
#define DIR_OPT                 ('d')
#define NAME_OPT                ('n')
#define EAGER_OPT               ('e')
#define STREAMING_OPT           ('s')

#define BASE_CLI_OPT_STR        "d:ehn:qsvV"

typedef enum cli_handling_result {
  CLI_SUCCESS,
  CLI_UNRECOGNIZED,
  CLI_HELP_MESSAGE
} cli_res_t;

typedef struct common_cli_opts {
  unsigned long long opt_set_flags;  // Bitvector recording set options
  size_t buf_offset;    // Index of the end of the string in the buffers
  char *cnf_file_path;  // Typically points to a string in `argv[]`
  char *dsr_file_path;  // Typically points to a string in `argv[]`
  char *lsr_file_path;  // Typically points to a string in `argv[]`
  char cnf_file_path_buf[MAX_FILE_PATH_LEN];
  char dsr_file_path_buf[MAX_FILE_PATH_LEN];
  char lsr_file_path_buf[MAX_FILE_PATH_LEN];
} cli_opts_t;

void cli_init(cli_opts_t *cli);
cli_res_t cli_handle_opt(cli_opts_t *cli, int option, int optopt, char *optarg);

int cli_is_name_opt_set(cli_opts_t *cli);
int cli_is_dir_opt_set(cli_opts_t *cli);

void cli_concat_path_extensions(cli_opts_t *cli,
                                char *cnf_ext, char *dsr_ext, char *lsr_ext);

#endif /* _DSR_TRIM_CLI_H_ */