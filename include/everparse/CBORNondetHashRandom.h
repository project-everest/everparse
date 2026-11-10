/* Hand-written, unverified convenience wrapper around the verified
 * cbor_nondet_parse_bounded_hash: draws a fresh random SipHash key from
 * the operating system, and falls back to the verified sort-based
 * cbor_nondet_parse_bounded_sort if no random key can be obtained. In
 * both cases, the result only depends on the input and the bounds (the
 * scratch spaces must satisfy cbor_nondet_bounded_hash_scratch_ok,
 * which implies cbor_nondet_bounded_sort_scratch_ok.) This function
 * allocates nothing. See also cbor_nondet_parse_bounded_hash_alloc_random
 * below, which allocates its scratch spaces.
 *
 * Random key sources: BCryptGenRandom on Windows (link with bcrypt),
 * arc4random_buf on BSDs and macOS, getrandom on Linux (glibc >= 2.25).
 * Define CBOR_NONDET_HASH_RANDOM_KEY(k) to a custom expression filling
 * the uint64_t[2] array k and returning nonzero on success, to override.
 */
#ifndef CBOR_NONDET_HASH_RANDOM_H
#define CBOR_NONDET_HASH_RANDOM_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "CBORNondet.h"

#if !defined(CBOR_NONDET_HASH_RANDOM_KEY)
#if defined(_WIN32)
#include <windows.h>
#include <bcrypt.h>
static inline int cbor_nondet_hash_random_key(uint64_t k[2]) {
  return BCRYPT_SUCCESS(BCryptGenRandom(NULL, (PUCHAR)k, 2 * sizeof(uint64_t),
                                        BCRYPT_USE_SYSTEM_PREFERRED_RNG));
}
#elif defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__) || \
    defined(__NetBSD__) || defined(__DragonFly__)
#include <stdlib.h>
static inline int cbor_nondet_hash_random_key(uint64_t k[2]) {
  arc4random_buf(k, 2 * sizeof(uint64_t));
  return 1;
}
#elif defined(__linux__)
#include <sys/random.h>
static inline int cbor_nondet_hash_random_key(uint64_t k[2]) {
  size_t got = 0;
  while (got < 2 * sizeof(uint64_t)) {
    ssize_t r = getrandom((uint8_t *)k + got, 2 * sizeof(uint64_t) - got, 0);
    if (r <= 0) return 0;
    got += (size_t)r;
  }
  return 1;
}
#else
static inline int cbor_nondet_hash_random_key(uint64_t k[2]) {
  (void)k;
  return 0;
}
#endif
#define CBOR_NONDET_HASH_RANDOM_KEY(k) cbor_nondet_hash_random_key(k)
#endif

static inline bool cbor_nondet_parse_bounded_hash_random(
    size_t map_depth_bound, size_t map_length_bound, bool check_map_key_bound,
    size_t map_key_bound, size_t *scratch,
    size_t scratch_len, uint64_t *hash_scratch, size_t hash_scratch_len,
    uint8_t **pinput, size_t *plen, cbor_raw *dest) {
  uint64_t k[2];
  if (CBOR_NONDET_HASH_RANDOM_KEY(k))
    return cbor_nondet_parse_bounded_hash(map_depth_bound, map_length_bound,
                                          check_map_key_bound, map_key_bound,
                                          k[0], k[1], scratch, scratch_len,
                                          hash_scratch, hash_scratch_len,
                                          pinput, plen, dest);
  if (hash_scratch == NULL ||
      !cbor_nondet_bounded_hash_scratch_ok(map_depth_bound, map_length_bound,
                                           scratch_len, hash_scratch_len))
    return false;
  return cbor_nondet_parse_bounded_sort(map_depth_bound, map_length_bound,
                                        check_map_key_bound, map_key_bound,
                                        scratch, scratch_len, pinput, plen,
                                        dest);
}

/* Same as cbor_nondet_parse_bounded_hash_random, but with the scratch
 * spaces allocated on the heap by the verified
 * cbor_nondet_parse_bounded_{hash,sort}_alloc (which may also fail
 * because of allocation failure.) */
static inline bool cbor_nondet_parse_bounded_hash_alloc_random(
    size_t map_depth_bound, size_t map_length_bound, bool check_map_key_bound,
    size_t map_key_bound, uint8_t **pinput, size_t *plen, cbor_raw *dest) {
  uint64_t k[2];
  if (CBOR_NONDET_HASH_RANDOM_KEY(k))
    return cbor_nondet_parse_bounded_hash_alloc(
        map_depth_bound, map_length_bound, check_map_key_bound, map_key_bound,
        k[0], k[1], pinput, plen, dest);
  return cbor_nondet_parse_bounded_sort_alloc(
      map_depth_bound, map_length_bound, check_map_key_bound, map_key_bound,
      pinput, plen, dest);
}

#endif
