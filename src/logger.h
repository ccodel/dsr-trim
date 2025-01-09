/**
 * @file logger.h
 * @brief A logging tool with levels of verbosity.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-08
 */

#ifndef _LOGGER_H_
#define _LOGGER_H_

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
void log_msg(vlevel_t level, const char *format, ...);

// Logs a message to `stderr`.
void log_err(const char *format, ...);

#endif /* _LOGGER_H_ */