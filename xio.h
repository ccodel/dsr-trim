/**
 * @file xio.h
 * @brief "Safer" file I/O operations that error on failure.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-11
 */

#include <stdio.h>

#ifndef _XIO_H_
#define _XIO_H_

FILE *xfopen(const char *path, const char *mode);

#endif /* _XIO_H_ */
