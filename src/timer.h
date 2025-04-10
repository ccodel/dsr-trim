/**
 * @file timer.h
 * @brief Timer utility for measuring wall-clock time and setting timeouts.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-04-04
 */

#ifndef _TIMER_H_
#define _TIMER_H_

#include <sys/time.h>

#define TOTAL_TIMERS     (3)

typedef enum timer_types {
  TIMER_GLOBAL = 0,
  TIMER_LOCAL = 1,
} timer_type_t;

typedef struct timer {
  struct timeval timers[TOTAL_TIMERS];
} timer_t;

void timer_init(timer_t *t);
void timer_record(timer_t *t, timer_type_t ty);
void timer_print_elapsed(timer_t *t, timer_type_t ty, char *prefix);

#endif /* _TIMER_H_ */