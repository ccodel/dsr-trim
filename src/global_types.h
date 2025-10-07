/**
 * @file global_types.h
 * @brief Global type definitions and macros.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-01-05
 */

#ifndef _GLOBAL_TYPES_H_
#define _GLOBAL_TYPES_H_

#include <stdlib.h>
#include <stdio.h>

#ifndef MIN
#define MIN(x, y)  (((x) < (y)) ? (x) : (y))
#endif

#ifndef MAX
#define MAX(x, y)  (((x) > (y)) ? (x) : (y))
#endif

#ifndef MSB
#define MSB32                     (1  << 31)
#define MSB64                     (1L << 63)

#define INT_SET_BIT(s)            (1  << (s))
#define LONG_SET_BIT(s)           (1L << (s))
#endif

#ifndef llong
typedef long long llong;
typedef unsigned long long ullong;
#endif

typedef unsigned int uint;
typedef unsigned long ulong;

// If the SR proofs are massive, then `long long`s should be used.
// But for most purposes, `int`s can be used instead.
#ifdef LONGTYPE
typedef llong srid_t;
typedef ullong usrid_t;
#define SRID_MSB         MSB64
#define SRID_MIN         LLONG_MIN
#define SRID_MAX         LLONG_MAX
#define SRID_NEG_ONE     (-1L)
#else
typedef int srid_t;
typedef unsigned int usrid_t;
#define SRID_MSB         MSB32
#define SRID_MIN         INT_MIN
#define SRID_MAX         INT_MAX
#define SRID_NEG_ONE     (-1)
#endif

/** Resizes an "allocation size value" when the container gets full. */
#define RESIZE(x)        (((x) * 3) >> 1)

#define RESIZE_ARR(arr, alloc_size, size, data_size)       do {                \
    if (size >= alloc_size) {                                                  \
      alloc_size = RESIZE(size);                                               \
      arr = xrealloc(arr, alloc_size * data_size);                             \
    }                                                                          \
  } while (0)

#define RESIZE_ARR_CONCAT(arr, data_size)                                      \
  RESIZE_ARR(arr, arr ## _alloc_size, arr ## _size, data_size)

#define INSERT_ARR_ELT(arr, alloc_size, size, data_size, elt)    do {          \
    RESIZE_ARR(arr, alloc_size, size, data_size);                              \
    arr[size] = elt;                                                           \
    size++;                                                                    \
  } while (0)

#define INSERT_ARR_ELT_CONCAT(arr, data_size, elt)                             \
  INSERT_ARR_ELT(arr, arr ## _alloc_size, arr ## _size, data_size, elt)

#define RECALLOC_ARR(arr, alloc_size, size, data_size)     do {                \
    if (size >= alloc_size) {                                                  \
      arr = xrecalloc(arr, alloc_size * data_size,                             \
        RESIZE(size) * data_size);                                             \
      alloc_size = RESIZE(size);                                               \
    }                                                                          \
  } while (0)

#define RESIZE_MEMSET_ARR(arr, alloc_size, size, data_size, c) do {            \
    if (size >= alloc_size) {                                                  \
      arr = xrealloc_memset(arr, alloc_size * data_size,                       \
        RESIZE(size) * data_size, c);                                          \
      alloc_size = RESIZE(size);                                               \
    }                                                                          \
  } while (0)

#endif /* _GLOBAL_TYPES_H_ */