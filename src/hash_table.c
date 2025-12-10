/**
 * @file hash_table.c
 * @brief A separate-chaining resizing hash table with user-defined data.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-12-09
 */

#include <stdint.h>    // For `uint8_t` in debug print functions
#include <string.h>

#include "hash_table.h"
#include "xmalloc.h"
#include "logger.h"

// Returns the index of `hash` in the buckets array with `num_buckets` buckets.
#define HASH_IDX(hash, num_buckets)   ((hash) % ((uint) num_buckets))

// Returns the pointer to the bucket in `ht->buckets` corresponding to `hash`.
#define BUCKET(hash, ht)   (&(ht)->buckets[HASH_IDX(hash, (ht)->num_buckets)])

// Returns the size of a single entry with `entry_data_size` data bytes.
#define ENTRY_SIZE(entry_data_size)   (sizeof(ht_entry_t) + (entry_data_size))

// Returns the pointer to the entry at index `idx` in `bucket`.
#define ENTRY_I(bucket, idx, entry_data_size)           \
  (ht_entry_t *) ((char *) (bucket)->entries +          \
    (idx) * ENTRY_SIZE(entry_data_size))

// Returns the pointer beyond the last entry in `bucket`.
#define NEW_ENTRY_PTR(bucket, entry_data_size)          \
  ENTRY_I(bucket, (bucket)->size, entry_data_size)

/**
 * @brief Initializes the hash table with the specified number of buckets.
 * 
 * Once a hash table has been initialized, it cannot be initialized again
 * unless a call to `ht_free()` is made first, or else memory will be leaked.
 * 
 * @param ht  The hash table to initialize.
 * @param entry_size  The number of bytes in each entry's `data` field.
 * @param num_buckets The number of buckets to allocate in the hash table.
 */
void ht_init_with_size(ht_t *ht, int entry_data_size, int num_buckets) {
  FATAL_ERR_IF(num_buckets <= 0, "Number of HT buckets must be positive.");
  FATAL_ERR_IF(entry_data_size <= 0, "Hash table entry size must be positive.");
  ht->entry_data_size = entry_data_size;
  ht->num_buckets = num_buckets;
  ht->num_entries = 0;
  ht->buckets = xcalloc(num_buckets, sizeof(ht_bucket_t));
}

/**
 * @brief Initializes the hash table with `DEFAULT_INIT_HT_SIZE` buckets.
 * 
 * See `ht_init_with_size()` for more details.
 * 
 * @param ht  The hash table to initialize.
 * @param entry_data_size  The number of bytes in each entry's `data` field.
 */
void ht_init(ht_t *ht, int entry_data_size) {
  ht_init_with_size(ht, entry_data_size, DEFAULT_INIT_HT_SIZE);
}

// Frees the memory for a single bucket, i.e., the array of entries.
static void ht_free_bucket(ht_bucket_t *bucket) {
  if (bucket->entries != NULL) {
    free(bucket->entries);
  }
}

// Frees the memory for all `num_buckets` in the `buckets` array,
// and then frees the `buckets` array itself.
static void ht_free_buckets(ht_bucket_t *buckets, int num_buckets) {
  for (int i = 0; i < num_buckets; i++) {
    ht_free_bucket(&buckets[i]);
  }

  free(buckets);
}

/**
 * @brief Frees all memory allocated by the hash table. This includes entries.
 * 
 * Also initializes its fields back to zero.
 * 
 * @param ht  The hash table to free.
 */
void ht_free(ht_t *ht) {
  ht_free_buckets(ht->buckets, ht->num_buckets);
  memset(ht, 0, sizeof(ht_t));
}

// Resizes the bucket if it has reached capacity.
// If the bucket is NULL, allocates space for `INIT_HT_BUCKET_SIZE` entries.
static void ht_resize_bucket(ht_bucket_t *bucket, int entry_data_size) {
  if (bucket->size >= bucket->alloc_size) {
    if (bucket->alloc_size == 0) {
      bucket->alloc_size = INIT_HT_BUCKET_SIZE;
    } else {
      bucket->alloc_size *= 2;
    }
    
    size_t s = bucket->alloc_size * ENTRY_SIZE(entry_data_size);
    bucket->entries = xrealloc(bucket->entries, s);
  }
}

// Returns a pointer to the next available entry in the bucket,
// resizing the bucket if necessary.
static ht_entry_t *ht_get_next_available_entry(ht_bucket_t *bucket, int entry_data_size) {
  ht_resize_bucket(bucket, entry_data_size);
  ht_entry_t *entry = NEW_ENTRY_PTR(bucket, entry_data_size);
  return entry;
}

// Inserts the data into a new entry in the appropriate bucket without resizing.
// (The bucket may get resized to fit the new entry.)
static void ht_insert_no_resize(ht_t *ht, uint hash, void *data) {
  uint hash_idx = HASH_IDX(hash, ht->num_buckets);
  ht_bucket_t *bucket = &ht->buckets[hash_idx];
  ht_entry_t *entry = ht_get_next_available_entry(bucket, ht->entry_data_size);
  entry->hash = hash;
  memcpy(entry->data, data, ht->entry_data_size);
  bucket->size++;
  ht->num_entries++;
}

// Takes the entries from the source buckets and re-inserts them into the
// destination buckets according to their hashes.
// Does NOT free `src_bs` on return.
static void ht_rehash(ht_bucket_t *src_bs, int src_num_buckets,
        ht_bucket_t *dst_bs, int dst_num_buckets, int entry_data_size) {
  for (int i = 0; i < src_num_buckets; i++) {
    ht_bucket_t *src_b = &src_bs[i];
    int src_size = src_b->size;
    for (int j = 0; j < src_size; j++) {
      ht_entry_t *src_e = ENTRY_I(src_b, j, entry_data_size);
      uint hash = HASH_IDX(src_e->hash, dst_num_buckets);
      ht_bucket_t *dst_b = &dst_bs[hash];
      ht_entry_t *dst_e = ht_get_next_available_entry(dst_b, entry_data_size);
      memcpy(dst_e, src_e, ENTRY_SIZE(entry_data_size));
      dst_b->size++;
    }
  }
}

static void ht_rehash_and_free(ht_bucket_t *src_bs, int src_num_buckets,
        ht_bucket_t *dst_bs, int dst_num_buckets, int entry_data_size) {
  ht_rehash(src_bs, src_num_buckets, dst_bs, dst_num_buckets, entry_data_size);
  ht_free_buckets(src_bs, src_num_buckets);
}

// Resizes the hash table to `new_num_buckets` buckets.
// Re-inserts all existing entries into their new buckets.
static void ht_resize(ht_t *ht, int new_num_buckets) {
  int old_num_buckets = ht->num_buckets;
  ht_bucket_t *old_buckets = ht->buckets;

  ht->num_buckets = new_num_buckets;
  ht->buckets = xcalloc(ht->num_buckets, sizeof(ht_bucket_t));

  ht_rehash_and_free(old_buckets, old_num_buckets,
      ht->buckets, ht->num_buckets, ht->entry_data_size);
}

// Doubles the number of buckets.
static void ht_resize_up(ht_t *ht) {
  ht_resize(ht, ht->num_buckets * 2);
}

// Halves the number of buckets.
static void ht_resize_down(ht_t *ht) {
  ht_resize(ht, ht->num_buckets / 2);
}

// Inserts a new entry with `hash`, potentially resizing the hash table first.
void ht_insert(ht_t *ht, uint hash, void *data) {
  if (ht->num_entries >= ht->num_buckets * LOAD_FACTOR) {
    ht_resize_up(ht);
  }

  ht_insert_no_resize(ht, hash, data);
}

/**
 * @brief Returns a pointer to the bucket for `hash`.
 * 
 * @note This pointer is not guaranteed to be valid after a resize/insert.
 */
ht_bucket_t *ht_get_bucket(ht_t *ht, uint hash) {
  return BUCKET(hash, ht);
}

// Returns the index of `entry` in the `bucket->entries` array.
static int ht_get_index_of_entry(ht_t *ht, ht_bucket_t *bucket, ht_entry_t *entry) {
  int chars_over = ((char *) entry) - ((char *) bucket->entries);
  int index = chars_over / ENTRY_SIZE(ht->entry_data_size);
  return index;
}

/**
 * @brief Finds the next entry in the bucket with the specified hash.
 *        If `prev_entry` is not `NULL`, the search starts at the entry
 *        right after it. If `prev_entry` is `NULL`, the search starts
 *        at the beginning of the bucket.
 * 
 * @note The pointer to the entry is not guaranteed to be valid after a resize/insert.
 */
ht_entry_t *ht_get_entry_in_bucket(
          ht_t *ht, ht_bucket_t *bucket, uint hash, ht_entry_t *prev_entry) {
  int index;
  if (prev_entry == NULL) {
    index = 0;
  } else {
    index = ht_get_index_of_entry(ht, bucket, prev_entry) + 1;
  }

  for (; index < bucket->size; index++) {
    ht_entry_t *e = ENTRY_I(bucket, index, ht->entry_data_size);
    if (e->hash == hash) {
      return e;
    }
  }

  return NULL;
}

/**
 * @brief Returns a pointer to the next entry with the specified hash
 *        in the bucket corresponding to `hash`. If `prev_entry` is not `NULL`,
 *        the search starts at the entry right after it. If `prev_entry` is
 *       `NULL`, the search starts at the beginning of the bucket.
 * 
 * @note The pointer to the entry is not guaranteed to be valid after a resize/insert.
 */
ht_entry_t *ht_get_entry(ht_t *ht, uint hash, ht_entry_t *prev_entry) {
  ht_bucket_t *bucket = BUCKET(hash, ht);
  return ht_get_entry_in_bucket(ht, bucket, hash, prev_entry);
}

/**
 * @brief Removes the entry from its bucket.
 * 
 * @note After removal, the `bucket` pointer may no longer be valid.
 */
void ht_remove_entry_in_bucket(ht_t *ht, ht_bucket_t *bucket, ht_entry_t *entry) {
  ht_entry_t *last_e = ENTRY_I(bucket, bucket->size - 1, ht->entry_data_size);
  if (entry != last_e) {
    memcpy(entry, last_e, ENTRY_SIZE(ht->entry_data_size));
  }

  bucket->size--;
  ht->num_entries--;

  // TODO: Downsize bucket?
  // TODO: Downsize hash table. Possibly store initial number of buckets?
  // ht_resize_down(ht);
}

/**
 * @brief Removes the entry from its bucket.
 */
void ht_remove_entry(ht_t *ht, ht_entry_t *entry) {
  uint hash = entry->hash;
  ht_bucket_t *bucket = BUCKET(hash, ht);
  ht_remove_entry_in_bucket(ht, bucket, entry);
}

// Prints the entry's information and data in hex format.
void dbg_print_ht_entry(ht_entry_t *entry, int entry_data_size) {
  logc_raw("HT Entry - Hash: %u, Data: ", entry->hash);
  uint8_t *data_bytes = (uint8_t *) entry->data;
  for (int i = 0; i < entry_data_size; i++) {
    logc_raw("%02X ", data_bytes[i]);
  }
  logc_raw("\n");
}

void dbg_print_ht_bucket(ht_bucket_t *bucket, int entry_data_size) {
  logc_raw("HT Bucket - Size/alloc: %d/%d\n", bucket->size, bucket->alloc_size);
  for (int i = 0; i < bucket->size; i++) {
    ht_entry_t *entry = ENTRY_I(bucket, i, entry_data_size);
    dbg_print_ht_entry(entry, entry_data_size);
  }
}

void dbg_print_ht(ht_t *ht) {
  logc_raw("Hash Table - Num Buckets: %d, Num Entries: %d, Entry Data Size: %d\n",
           ht->num_buckets, ht->num_entries, ht->entry_data_size);
  for (int i = 0; i < ht->num_buckets; i++) {
    ht_bucket_t *bucket = &ht->buckets[i];
    if (bucket->size == 0) continue;
    logc_raw("Bucket %d:\n", i);
    dbg_print_ht_bucket(&ht->buckets[i], ht->entry_data_size);
  }
}