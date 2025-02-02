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

void log_raw(vlevel_t level, const char *format, ...) {
  if (level <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    vfprintf(stdout, format, ap);
    va_end(ap);
  }
}

void log_msg(vlevel_t level, const char *format, ...) {
  if (level <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    fprintf(stdout, "c ");
    vfprintf(stdout, format, ap);
    fprintf(stdout, "\n");
    va_end(ap);
  }
}

void logc(const char *format, ...) {
  if (VL_NORMAL <= verbosity_level) {
    va_list ap;
    va_start(ap, format);
    fprintf(stdout, "c ");
    vfprintf(stdout, format, ap);
    fprintf(stdout, "\n");
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

void log_fatal_err(const char *format, ...) {
  va_list ap;
  va_start(ap, format);
  fprintf(stderr, "Fatal error: ");
  vfprintf(stderr, format, ap);
  va_end(ap);
  fprintf(stderr, "\n");
  exit(1);
}