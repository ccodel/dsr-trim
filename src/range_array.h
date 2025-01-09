/**
 * @file range_array.h
 * @brief A "two-dimensional" array that stores data in a flat array
 *        and index "pointers" in another.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-05
 */

#ifndef _RANGE_ARRAY_H_
#define _RANGE_ARRAY_H_

#include "global_types.h"

/**
 * @brief The range array.
 * 
 * The `data` field must be a `void *` because we don't know the size of
 * the data stored within. Almost all use cases will have the data be
 * either an `int` or an `srid_t`, which can be a `long long`.
 */
typedef struct range_array {
  void *data;
  srid_t *indexes; // TODO: Should it be `srid_t` or `ullong`?
  ullong data_size;
  ullong data_alloc_size;
  ullong indexes_size;
  ullong indexes_alloc_size;
  uint elts_size; // Fixed size for elements in the `data` array.
} range_array_t;

void ra_init(range_array_t *ra, ullong init_num_elts, 
                      ullong init_num_ranges, uint elts_size);

// Clears any committed indexes or data.
void ra_reset(range_array_t *ra);

// Does validation that the size of the element matches `elts_size` from init.

void ra_insert_int_elt(range_array_t *ra, int elt);
void ra_insert_long_elt(range_array_t *ra, llong elt);
void ra_insert_srid_elt(range_array_t *ra, srid_t elt);
void ra_commit_range(range_array_t *ra);
void ra_commit_empty_ranges_until(range_array_t *ra, ullong range_index);

void *ra_get_range_start(range_array_t *ra, ullong range_index);
ullong ra_get_range_size(range_array_t *ra, ullong range_index);

#endif /* _RANGE_ARRAY_H_ */