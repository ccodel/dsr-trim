/**
 * @file hash_table.c
 * @brief A standard non-resizing separate chaining hash table.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-25
 */

#include "hash_table.h"
#include "xmalloc.h"
#include "logger.h"

void ht_init(ht_t *ht, uint load) {
  uint alloc_size = MAX(load, INIT_HT_BUCKETS_SIZE);
  ht->buckets = xcalloc(alloc_size, sizeof(htb_t));
  ht->buckets_alloc_size = alloc_size;
}

void ht_insert(ht_t *ht, uint hash, srid_t data) {
  hash = hash % ht->buckets_alloc_size;
  htb_t *b = &ht->buckets[hash];

  // Allocate space for the bucket's entries, if none exist yet
  if (b->entries == NULL) {
    b->size = 0;
    b->alloc_size = INIT_HT_BUCKET_SIZE;
    b->entries = xmalloc(b->alloc_size * sizeof(hte_t));
  }

  // Resize the bucket's entries if we've run out of space
  if (b->size >= b->alloc_size) {
    b->alloc_size = RESIZE(b->size);
    b->entries = xrealloc(b->entries, b->alloc_size * sizeof(hte_t));
  }

  // Store the data
  b->entries[b->size].data = data;
  b->size++;
}

htb_t *ht_get_bucket(ht_t *ht, uint hash) {
  return &ht->buckets[hash % ht->buckets_alloc_size];
}

// Remove the entry at the provided index.
void ht_remove_at_index(htb_t *bucket, uint index) {
  FATAL_ERR_IF(index >= bucket->size, "Index out of bounds.");

  if (bucket->size > 1) {
    bucket->entries[index] = bucket->entries[bucket->size - 1];
  }

  bucket->size--;
}