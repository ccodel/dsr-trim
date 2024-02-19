/** @file xmalloc.c
 *  @brief Exit() wrappers around malloc() family functions.
 *
 *  When memory must be allocated and execution cannot occur after a
 *  failed allocation, then the xmalloc() family functions should be
 *  used. If a malloc() family function returns a NULL pointer, then
 *  exit(-1) is called, ending execution. Just before calling exit(-1),
 *  an error message is printed to stderr.
 *
 *  @author Joseph Reeves (jereeves@andrew.cmu.edu)
 *  @author Cayden Codel  (ccodel@andrew.cmu.edu)
 *
 *  @bug No known bugs.
 */

#include <stdlib.h>
#include <stdio.h>

#include "xmalloc.h"

/** @brief Exit() mechanism in use by all xmalloc() family functions.
 *
 *  Mainly just in place to reduce the amount of duplicated fprintf()ing.
 *
 *  @param ptr  The pointer that was allocated, to be checked against NULL.
 *  @param func A string of the function name that failed.
 */
#define NULL_POINTER(ptr, func) \
  if ((ptr) == NULL) {                                   \
    fprintf(stderr, "Ran out of memory on %s\n", func);  \
    exit(-1);                                            \
  }


/** @brief Exit() wrapper around calloc().
 *
 *  @param count The number of elements to allocate.
 *  @param size  The size of each element to allocate, in bytes.
 *  @return The result of calloc().
 */
void *xcalloc(size_t count, size_t size) {
  void *ptr = calloc(count, size);
  NULL_POINTER(ptr, "xcalloc");
  return ptr;
}


/** @brief Exit() wrapper around malloc().
 *
 *  @param size The size of the memory to allocate, in bytes.
 *  @return The result of malloc().
 */
void *xmalloc(size_t size) {
  void *ptr = malloc(size);
  NULL_POINTER(ptr, "xmalloc");
  return ptr;
}


/** @brief Exit() wrapper around realloc().
 *
 *  @param ptr  The old pointer.
 *  @param size The size of the new pointer, in bytes.
 *  @return The result of realloc().
 */
void *xrealloc(void *ptr, size_t size) {
  void *new_ptr = realloc(ptr, size);
  NULL_POINTER(new_ptr, "xrealloc");
  return new_ptr;
}


/** @brief Exit() wrapper around reallocf().
 *
 *  Because the behavior of reallocf() is to free the provided pointer if
 *  the new pointer cannot be allocated, due to calling exit(-1) on memory
 *  allocation, the pointer will not be freed. Thus, the behavior of
 *  xreallocf() is identical to xrealloc(), and so the latter is called in
 *  place of an implementation for the former.
 *
 *  @param ptr  The old pointer.
 *  @param size The size of the new pointer, in bytes.
 *  @return The result of reallocf().
 */
void *xreallocf(void *ptr, size_t size) {
  return xrealloc(ptr, size);
}


/** @brief Wrapper for free().
 *
 *  No pointer checks are required, so just calls free().
 *
 *  @param ptr  A pointer to be freed.
 */
void xfree(void *ptr) {
  free(ptr);
}
