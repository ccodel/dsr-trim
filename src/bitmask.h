/**
 * @file bitmask.h
 * @brief Bit-level bitmasking.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2026-01-13
 */

#ifndef _BITMASK_H_
#define _BITMASK_H_

#include <stddef.h>
#include <stdint.h>

// The size of a single "unit" of bits in the bitmask.
// NOTE: If this value changes (size), adjust `OFFSET` in `bitmask.c`.
#define BITMASK_UNIT    uint64_t

/**
 * @brief Bit-level bitmask.
 * 
 * The bitmask uses an array of `BITMASK_UNIT`s to store bits. The use of a
 * larger-than-`char` unit allows for more efficient memory usage
 * and bitwise operations, especially when mapping a function pointer
 * across a sparse bitmask.
 * 
 * To speed up clearing operations, the minimum and maximum indexes of
 * bits that are set are tracked. Both indexes are inclusive. They are indexes
 * into the `mask` array and are not the arguments to the bitmask functions.
 */
typedef struct bitmask {
  BITMASK_UNIT *mask;
  size_t alloc_size;      // Number of `BITMASK_UNIT` elements allocated.
  size_t min_index_set;   // Inclusive smallest set index in `mask`.
  size_t max_index_set;   // Inclusive largest set index in `mask`.
} bmask_t;

void bmask_init(bmask_t *bm, size_t num_elems);
void bmask_destroy(bmask_t *bm);
void bmask_clear(bmask_t *bm);

void bmask_set_bit(bmask_t *bm, size_t index);
void bmask_clear_bit(bmask_t *bm, size_t index);
int  bmask_is_bit_set(bmask_t *bm, size_t index);

void bmask_map_over_set_bits(bmask_t *bm, void (*fn)(size_t));

void dbg_print_bmask(bmask_t *bm);

#endif /* _BITMASK_H_ */