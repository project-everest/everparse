/* Hand-written, trusted implementation of the allocator interface
 * CBOR.Pulse.API.Nondet.C.Alloc (lib/everparse/cbor/pulse), used by the
 * verified cbor_nondet_parse_bounded_{sort,hash}_alloc to allocate their
 * scratch spaces once per call. This file is included by the extracted
 * CBORNondet.c; it is not meant to be included by users.
 *
 * Specification (trusted): cbor_nondet_malloc_T(n) returns either NULL,
 * or a pointer to a fresh, possibly uninitialized, array of n elements
 * of type T (in which case n fits in size_t), to be freed exactly once
 * with cbor_nondet_free_T. The count n is an element count, not a byte
 * count: the multiplication by sizeof(T) is checked for overflow here.
 *
 * Define CBOR_NONDET_CUSTOM_ALLOC to provide your own definitions of
 * these four functions (with external linkage) instead, e.g. to use a
 * custom allocator.
 */
#ifndef CBOR_NONDET_ALLOC_H
#define CBOR_NONDET_ALLOC_H

#include <stddef.h>
#include <stdint.h>

#ifndef CBOR_NONDET_CUSTOM_ALLOC

#include <stdlib.h>

size_t *cbor_nondet_malloc_size_t(uint64_t n) {
  if (n > (uint64_t)(SIZE_MAX / sizeof(size_t)))
    return NULL;
  return (size_t *)malloc(n == 0 ? 1 : (size_t)n * sizeof(size_t));
}

void cbor_nondet_free_size_t(size_t *p) { free(p); }

uint64_t *cbor_nondet_malloc_uint64_t(uint64_t n) {
  if (n > (uint64_t)(SIZE_MAX / sizeof(uint64_t)))
    return NULL;
  return (uint64_t *)malloc(n == 0 ? 1 : (size_t)n * sizeof(uint64_t));
}

void cbor_nondet_free_uint64_t(uint64_t *p) { free(p); }

#else

size_t *cbor_nondet_malloc_size_t(uint64_t n);
void cbor_nondet_free_size_t(size_t *p);
uint64_t *cbor_nondet_malloc_uint64_t(uint64_t n);
void cbor_nondet_free_uint64_t(uint64_t *p);

#endif

#endif
