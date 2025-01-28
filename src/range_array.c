/**
 * @file range_array.c
 * @brief A "two-dimensional" array that stores data in a flat array.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-05
 */

#include "range_array.h"
#include "xmalloc.h"
#include "logger.h"

/**
 * @brief Initializes the range array with an initial number of elements
 *        and the size of each element.
 */
void ra_init(range_array_t *ra, ullong init_num_elts, 
                      ullong init_num_ranges, uint elts_size) {
  ra->data_size = 0;
  ra->data_alloc_size = init_num_elts;
  ra->data = xmalloc(ra->data_alloc_size * elts_size);
  ra->indexes_size = 0;
  ra->indexes_alloc_size = init_num_ranges;
  ra->indexes = xmalloc(ra->indexes_alloc_size * sizeof(srid_t));
  ra->indexes[0] = 0; // Start the first range at the 0th index
  ra->elts_size = elts_size;
}

void ra_reset(range_array_t *ra) {
  ra->data_size = 0;
  ra->indexes_size = 0;
  ra->indexes[0] = 0; // Probably unnecessary, but just in case
}

/**
 * @brief Inserts an integer data element into `data` without updating `indexes`.
 * 
 * The caller must ensure that `ra` is not `NULL`.
 */
void ra_insert_int_elt(range_array_t *ra, int elt) {
  FATAL_ERR_IF(ra->elts_size != sizeof(int),
    "Range array expected an element size of something other than an int.");
  RESIZE_ARR(ra->data, ra->data_alloc_size, ra->data_size, ra->elts_size);
  ((int *) ra->data)[ra->data_size] = elt;
  ra->data_size++;
}

void ra_insert_long_elt(range_array_t *ra, llong elt) {
  FATAL_ERR_IF(ra->elts_size != sizeof(llong),
    "Range array expected an element size of something other than a long long.");
  RESIZE_ARR(ra->data, ra->data_alloc_size, ra->data_size, ra->elts_size);
  ((llong *) ra->data)[ra->data_size] = elt;
  ra->data_size++;
}

void ra_insert_srid_elt(range_array_t *ra, srid_t elt) {
  FATAL_ERR_IF(ra->elts_size != sizeof(srid_t),
    "Range array expected an element size of something other than an srid_t.");
  RESIZE_ARR(ra->data, ra->data_alloc_size, ra->data_size, ra->elts_size);
  ((srid_t *) ra->data)[ra->data_size] = elt;
  ra->data_size++;
}

/**
 * @brief Commits the set of uncommitted data elements by adding an index
 *        for the next range to `indexes`.
 * 
 * The caller must ensure that `ra` is not `NULL`.
 */
void ra_commit_range(range_array_t *ra) {
  /* 
   * Since we started the first index at 0, we instead point the index for
   * the next uncommitted range at where the next data element should go.
   * This has the effect of "capping off" the current range of data elements.
   */
  ra->indexes_size++;
  RESIZE_ARR(ra->indexes, ra->indexes_alloc_size, ra->indexes_size, sizeof(srid_t));
  ra->indexes[ra->indexes_size] = ra->data_size;
}

/**
 * @brief Commits empty ranges until the `range_index` is about to be committed.
 * 
 * This function should be called when the indexes between the current
 * `indexes_size` and the provided `range_index` should be empty.
 * 
 * The caller must ensure that `ra` is not `NULL`.
 */
void ra_commit_empty_ranges_until(range_array_t *ra, ullong range_index) {
  const ullong old_size = ra->indexes_size;
  if (old_size >= range_index) return;

  // In order to avoid inefficiently looping around `commit_range()`,
  // we instead anticipate the resize we need and then loop around
  // setting the `indexes` directly.
  ullong new_size = MAX(range_index + 1, old_size);
  RESIZE_ARR(ra->indexes, ra->indexes_alloc_size, new_size, sizeof(srid_t));
  for (ullong i = old_size; i <= range_index; i++) {
    ra->indexes[i] = ra->data_size;
  }
  
  ra->indexes_size = range_index;
}

/**
 * @brief "Forgets" an `amount` number of uncommitted data elements.
 * 
 * In rare cases, a caller might want to drop some number of uncommitted
 * data elements without resetting the range. This function shrinks the
 * number of uncommitted elements without affecting any data or any
 * other indexes.
 * 
 * @param ra 
 * @param amount 
 */
void ra_uncommit_data_by(range_array_t *ra, ullong amount) {
  ra->data_size -= amount;
}

void *ra_get_range_start(range_array_t *ra, ullong range_index) {
  if (range_index == 0) {
    return ra->data;
  }

  ullong offset;
  if (range_index == ra->indexes_size + 1) {
    offset = ra->data_size;
  } else {
    offset = ra->indexes[range_index];
  }

  if (ra->elts_size == sizeof(int)) {
    return ((int *) ra->data) + offset;
  } else {
    return ((llong *) ra->data) + offset;
  }
}

ullong ra_get_range_size(range_array_t *ra, ullong range_index) {
  if (range_index == ra->indexes_size) {
    return ra->data_size - ra->indexes[range_index];
  } else {
    return ra->indexes[range_index + 1] - ra->indexes[range_index];
  }
}