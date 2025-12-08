/**
 * @file logger.c
 * @brief A logging tool with levels of verbosity.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-08
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "logger.h"

vlevel_t verbosity_level = VL_NORMAL;
vlevel_t err_verbosity_level = VL_QUIET;

void log_raw(vlevel_t level, const char *format, ...) {
  if (level <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    vfprintf(stdout, format, ap);
    va_end(ap);
  }
}

static inline void log_args_with_c_and_newline(const char *format, va_list ap) {
  fprintf(stdout, "c ");
  vfprintf(stdout, format, ap);
  fprintf(stdout, "\n");
}

void log_msg(vlevel_t level, const char *format, ...) {
  if (level <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    log_args_with_c_and_newline(format, ap);
    va_end(ap);
  }
}

void logc(const char *format, ...) {
  if (VL_NORMAL <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    log_args_with_c_and_newline(format, ap);
    va_end(ap);
  }
}

void logc_raw(const char *format, ...) {
  if (VL_NORMAL <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    vfprintf(stdout, format, ap); 
    va_end(ap);
  }
}

void logv(const char *format, ...) {
  if (VL_VERBOSE <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    log_args_with_c_and_newline(format, ap);
    va_end(ap);
  }
}

void logv_raw(const char *format, ...) {
  if (VL_VERBOSE <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    vfprintf(stdout, format, ap); 
    va_end(ap);
  }
}

void log_err(const char *format, ...) {
  va_list ap;
  va_start(ap, format);
  fprintf(stderr, "Error: ");
  vfprintf(stderr, format, ap);
  fprintf(stderr, "\n");
  va_end(ap);
}

void log_err_raw(const char *format, ...) {
  va_list ap;
  va_start(ap, format);
  vfprintf(stderr, format, ap);
  va_end(ap);
}

void log_fatal_err(const char *format, ...) {
  va_list ap;
  va_start(ap, format);
  fprintf(stderr, "Fatal error: ");
  vfprintf(stderr, format, ap);
  va_end(ap);
  fprintf(stderr, "\n");
  exit(1);
}