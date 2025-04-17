/**
 * @file timer.c
 * @brief Timer utility for measuring wall-clock time and setting timeouts.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-04-04
 */

#include "timer.h"
#include "logger.h"
#include <string.h>

void timer_init(sr_timer_t *t) {
  FATAL_ERR_IF(t == NULL, "timer_init: sr_timer_t pointer is NULL");
  memset(t, 0, sizeof(sr_timer_t));
}

void timer_record(sr_timer_t *t, timer_type_t ty) {
  FATAL_ERR_IF(t == NULL, "record_time: sr_timer_t pointer is NULL");
  struct timeval *timer = &t->timers[ty];
  gettimeofday(timer, NULL);
}

static unsigned long long timer_get_elapsed_millisecs(sr_timer_t *t, timer_type_t ty) {
  FATAL_ERR_IF(t == NULL, "timer_get_millisecs: sr_timer_t pointer is NULL");

  struct timeval *start = &t->timers[ty];
  struct timeval *end = &t->timers[TOTAL_TIMERS - 1];
  gettimeofday(end, NULL);
  return ((end->tv_sec - start->tv_sec) * 1000000)
          + (end->tv_usec - start->tv_usec);
}

void timer_print_elapsed(sr_timer_t *t, timer_type_t ty, char *prefix) {
  unsigned long long elapsed = timer_get_elapsed_millisecs(t, ty);
  logc("%s took %.3f secs", prefix, ((double) elapsed) / 1000000.0);
}
