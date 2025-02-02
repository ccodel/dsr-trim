/**
 * @file logger.h
 * @brief A logging tool with levels of verbosity.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-08
 */

#ifndef _LOGGER_H_
#define _LOGGER_H_

#define FATAL_ERR_IF(cond, ...) do { \
  if (cond) { \
    log_fatal_err(__VA_ARGS__); \
  } \
} while (0)

/**
 * @brief The verbosity levels.
 * 
 * The corresponding message is printed if the global verbosity level
 * is at least as verbose as the level. For example, `VL_QUIET` messages
 * are always printed, while `VL_VERBOSE` messages are only printed when
 * the verbosity level is set to `VL_VERBOSE`.
 */
typedef enum verbosity_level {
  VL_QUIET = 0,
  VL_NORMAL = 1,
  VL_VERBOSE = 2
} vlevel_t;

// The global verbosity level. By default, it is set to `VL_NORMAL`.
extern vlevel_t verbosity_level;

// Logs a message to `stdout` if the provided `level` is `<= verbosity_level`.
// Does not begin with a `"c "` or end with a newline `'\n'`.
void log_raw(vlevel_t level, const char *format, ...);

// Logs a message to `stdout` if the provided `level` is `<= verbosity_level`.
// Begins the message with `"c "` and ends it with a newline `'\n'`.
void log_msg(vlevel_t level, const char *format, ...);

// Alias for `log_msg(VL_NORMAL, ...)`.
void logc(const char *format, ...);

// Logs a message to `stderr`.
// Begins the message with `"Error: "` and end the message with a newline `'\n'`.
void log_err(const char *format, ...);

// Logs a fatal error (along with a newline `'\n'`) and exits.
void log_fatal_err(const char *format, ...);

#endif /* _LOGGER_H_ */