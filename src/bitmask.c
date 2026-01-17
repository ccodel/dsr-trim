/**
 * @file bitmask.c
 * @brief Bit-level bitmasking.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2026-01-13
 */

#include <string.h>

#include "bitmask.h"
#include "global_types.h"
#include "logger.h"
#include "xmalloc.h"

#define BITMASK_ONE           (1L)
#define SIZEOF_UNIT           (sizeof(BITMASK_UNIT))
#define NUM_BITS_IN_UNIT      (SIZEOF_UNIT * 8)

// Index into the mask. In other words, the "bin" for the element.
#define INDEX(i)              ((i) / NUM_BITS_IN_UNIT)

// Offset into the mask unit. In other words, the "bit" for the element.
// NOTE: This is a manually-made mask, must be adjusted if `BITMASK_UNIT` does.
#define OFFSET(i)       ((i) & ((BITMASK_ONE << 6) - BITMASK_ONE))

////////////////////////////////////////////////////////////////////////////////

static void reset_min_max_indexes(bmask_t *bm) {
  bm->min_index_set = SIZE_MAX;
  bm->max_index_set = 0;
}

/**
 * @brief Initializes the bitmask and allocates memory.
 * 
 * Undefined behavior if `bmask_init()` is called twice without an
 * intervening call to `bmask_destroy()`.
 * 
 * @param bm A pointer to the `bmask_t` structure to initialize.
 * @param num_elems The number of elements the bitmask should track.
 */
void bmask_init(bmask_t *bm, size_t num_elems) {
  // Round the number of mask units based on the number of bits in a unit
  bm->alloc_size = (num_elems + NUM_BITS_IN_UNIT - 1) / NUM_BITS_IN_UNIT;
  bm->mask = xcalloc(bm->alloc_size, SIZEOF_UNIT);
  reset_min_max_indexes(bm);
}

/**
 * @brief Frees memory held by the bitmask and clears the struct.
 * 
 * It is undefined behavior if `destroy()` is called twice in a row
 * on the same object or before a call to` init()`.
 */
void bmask_destroy(bmask_t *bm) {
  xfree(bm->mask);
  memset(bm, 0, sizeof(bmask_t));
}

/**
 * @brief Clears all set bits from the mask.
 */
void bmask_clear(bmask_t *bm) {
  // Calculate the address range to clear
  if (bm->min_index_set <= bm->max_index_set) {
    memset(bm->mask + bm->min_index_set, 0, 
      (bm->max_index_set - bm->min_index_set + 1) * SIZEOF_UNIT);
    reset_min_max_indexes(bm);
  }
}

/**
 * @brief Sets the requested bit.
 * 
 * Allocates more memory for the mask if `index` lies out of bounds.
 */
void bmask_set_bit(bmask_t *bm, size_t index) {
  size_t mask_index = INDEX(index);

  // Reallocate additional memory, if necessary
  if (mask_index >= bm->alloc_size) {
    size_t old_size = bm->alloc_size;
    bm->alloc_size = RESIZE(mask_index);
    bm->mask = xrecalloc(bm->mask,
      old_size * SIZEOF_UNIT, bm->alloc_size * SIZEOF_UNIT);
  }

  // Set the bit inside the mask's unit
  size_t offset = OFFSET(index);
  bm->mask[mask_index] |= (BITMASK_ONE << offset);
  SET_MIN_LEFT(bm->min_index_set, mask_index);
  SET_MAX_LEFT(bm->max_index_set, mask_index);
}

void bmask_clear_bit(bmask_t *bm, size_t index) {
  size_t mask_index = INDEX(index);
  if (mask_index >= bm->alloc_size) {
    return;
  }

  size_t offset = OFFSET(index);
  BITMASK_UNIT and_mask = ~(BITMASK_ONE << offset);
  bm->mask[mask_index] &= and_mask;
}

static inline int bmask_is_bit_in_unit_set(BITMASK_UNIT unit, size_t offset) {
  BITMASK_UNIT and_mask = BITMASK_ONE << offset;
  return (unit & and_mask) != 0;
}

/**
 * @brief Returns a nonzero value if the requested index is set in the mask.
 * 
 * @return 0 if the bit isn't set, and a nonzero value otherwise.
 */
int bmask_is_bit_set(bmask_t *bm, size_t index) {
  size_t mask_index = INDEX(index);
  if (mask_index >= bm->alloc_size) {
    return 0;
  }

  // If no bit is set in the unit, then we can return 0 right away
  BITMASK_UNIT unit = bm->mask[mask_index];
  if (unit == 0) {
    return 0;
  } else {
    size_t offset = OFFSET(index);
    return bmask_is_bit_in_unit_set(unit, offset);
  }
}

void bmask_map_over_set_bits(bmask_t *bm, void (*fn)(size_t)) {
  // Uncomment these three groups of lines for verbose printing.
  // size_t min_index = SIZE_MAX;
  // size_t max_index = 0;

  for (size_t i = bm->min_index_set; i <= bm->max_index_set; i++) {
    BITMASK_UNIT unit = bm->mask[i];
    if (unit != 0) {
      BITMASK_UNIT set_bit = BITMASK_ONE;
      for (size_t offset = 0; offset < NUM_BITS_IN_UNIT; offset++) {
        if (unit & set_bit) {
          size_t index = i * NUM_BITS_IN_UNIT + offset;
          fn(index);
          // SET_MIN_LEFT(min_index, index);
          // SET_MAX_LEFT(max_index, index);
        }

        set_bit <<= 1;
      }
    }
  }

  // logv("Mapping over set bits in bitmask: min index = %zu, max index = %zu",
  //     min_index, max_index);
}

void dbg_print_bmask(bmask_t *bm) {
  logc_raw("c Bitmask (alloc_size = %zu, num_bits = %zu):",
      bm->alloc_size, bm->alloc_size * NUM_BITS_IN_UNIT);

  if (bm->min_index_set > bm->max_index_set) {
    logc_raw(" [no bits set]\n");
    return;
  }

  size_t num_indexes = bm->alloc_size;
  for (size_t i = 0; i < num_indexes; i++) {
    if (bm->mask[i] != 0) {
      logc_raw(" [%zu] ", i * NUM_BITS_IN_UNIT);
      for (size_t bit = 0; bit < NUM_BITS_IN_UNIT; bit++) {
        if (bmask_is_bit_in_unit_set(bm->mask[i], bit)) {
          logc_raw("1");
        } else {
          logc_raw("-");
        }
      }
    }
  }

  logc_raw("\n");
}