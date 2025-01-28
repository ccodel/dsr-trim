/**
 * @file hash_table.h
 * @brief A standard non-resizing separate chaining hash table.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-25
 */

#ifndef _HASH_TABLE_H_
#define _HASH_TABLE_H_

#include "global_types.h"

#define INIT_HT_BUCKETS_SIZE   (1 << 16)
#define INIT_HT_BUCKET_SIZE    (4)

// To implement re-sizing, storing the hash might be useful

typedef struct hash_table_entry {
  srid_t data;
} hte_t;

typedef struct hash_table_bucket {
  hte_t *entries;
  uint size;
  uint alloc_size;
 } htb_t;

typedef struct chaining_hash_table {
  htb_t *buckets;
  uint buckets_alloc_size;
  // uint num_entries;
} ht_t;

void ht_init(ht_t *ht, uint load);
void ht_insert(ht_t *ht, uint hash, srid_t data);

htb_t *ht_get_bucket(ht_t *ht, uint hash);
void ht_remove_at_index(htb_t *bucket, uint index);

#endif /* _HASH_TABLE_H_ */
