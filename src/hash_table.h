/**
 * @file hash_table.h
 * @brief A separate-chaining resizing hash table with user-defined data.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-12-09
 */

#ifndef _HASH_TABLE_H_
#define _HASH_TABLE_H_

#include "global_types.h"

#define DEFAULT_INIT_HT_SIZE    (1 << 16)
#define INIT_HT_BUCKET_SIZE     (4)

// Resize when `(ht->num_entries * LOAD_FACTOR >= ht->num_buckets`.
// In other words, when there are `LOAD_FACTOR` times as many entries as
// hash table buckets, the number of buckets is doubled.
#define LOAD_FACTOR             (4)

/**
 * @brief An entry in the hash table.
 * 
 * Each entry stores its own hash so that it can be re-hashed into a table
 * on resize.
 * 
 * @note The `data` field is a flexible array member, and is only 4-byte
 *       aligned. If the data is a struct with a different alignment,
 *       use `memcpy()` to copy the contents instead of de-referencing
 *       a pointer to avoid alignment issues.
 */
typedef struct hash_table_entry {
  uint hash;
  char data[];  // User data, in an unspecified "flexible array member" field
} ht_entry_t;

// A bucket is a contiguous array of hash table entries.
typedef struct hash_table_bucket {
  ht_entry_t *entries;
  int size;           // The size, i.e., the number of stored entries.
  int alloc_size;     // The the number of possible entries.
} ht_bucket_t;

// A hash table is a contiguous array of buckets.
typedef struct hash_table {
  ht_bucket_t *buckets;
  int num_buckets;        // The number of buckets in the array.
  int num_entries;        // The number of entries currently stored.
  int entry_data_size;    // Size of each entry's `data` field, in bytes.
} ht_t;

void ht_init_with_size(ht_t *ht, int entry_data_size, int num_buckets);
void ht_init(ht_t *ht, int entry_data_size);
void ht_free(ht_t *ht);

void ht_insert(ht_t *ht, uint hash, void *data);

ht_bucket_t *ht_get_bucket(ht_t *ht, uint hash);

ht_entry_t *ht_get_entry_in_bucket(ht_t *ht, ht_bucket_t *bucket, uint hash, ht_entry_t *prev_entry);
ht_entry_t *ht_get_entry(ht_t *ht, uint hash, ht_entry_t *prev_entry);

void ht_remove_entry_in_bucket(ht_t *ht, ht_bucket_t *bucket, ht_entry_t *entry);
void ht_remove_entry(ht_t *ht, ht_entry_t *entry);

void dbg_print_ht_entry(ht_entry_t *entry, int entry_data_size);
void dbg_print_ht_bucket(ht_bucket_t *bucket, int entry_data_size);
void dbg_print_ht(ht_t *ht);

#endif /* _HASH_TABLE_H_ */
