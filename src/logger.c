/**
 * @file logger.c
 * @brief A logging tool with levels of verbosity.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-08
 */

#include <stdio.h>
#include <stdarg.h>

#include "logger.h"

vlevel_t verbosity_level = VL_NORMAL;

void log_msg(vlevel_t level, const char *format, ...) {
  if (level <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    vfprintf(stdout, format, ap);
    va_end(ap);
  }
}

void log_err(const char *format, ...) {
  va_list ap;
  va_start(ap, format);
  vfprintf(stderr, format, ap);
  va_end(ap);
}