/* CBOR emission helpers and a small PRNG shared by tests and benchmarks. */
#ifndef DUPCHECK_GEN_H
#define DUPCHECK_GEN_H
#include <stdint.h>
#include <stddef.h>
#include <string.h>

static uint64_t rng_state = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rng(void) {
  uint64_t x = rng_state;
  x ^= x << 13; x ^= x >> 7; x ^= x << 17;
  return rng_state = x;
}
static inline uint64_t rng_below(uint64_t n) { return n ? rng() % n : 0; }

/* Head with an explicit argument width: 0 = minimal (or immediate), else
 * 1, 2, 4 or 8 bytes (non-minimal allowed by nondet CBOR when it fits). */
static size_t emit_head_w(uint8_t *b, size_t o, uint8_t maj, uint64_t v,
                          unsigned w) {
  if (maj == 7) w = 0;          /* simple values: shortest form only */
  if (w == 0) {
    if (v < 24) { b[o++] = (uint8_t)(maj << 5 | v); return o; }
    w = v <= 0xff ? 1 : v <= 0xffff ? 2 : v <= 0xffffffffULL ? 4 : 8;
  }
  unsigned ai = w == 1 ? 24 : w == 2 ? 25 : w == 4 ? 26 : 27;
  b[o++] = (uint8_t)(maj << 5 | ai);
  for (int i = (int)w - 1; i >= 0; i--) b[o++] = (uint8_t)(v >> (8 * i));
  return o;
}
static size_t emit_head(uint8_t *b, size_t o, uint8_t maj, uint64_t v) {
  return emit_head_w(b, o, maj, v, 0);
}
/* A random legal width for v (non-minimal encodings included). */
static unsigned rand_width(uint64_t v) {
  unsigned ws[5], k = 0;
  ws[k++] = 0;
  if (v <= 0xff) ws[k++] = 1;
  if (v <= 0xffff) ws[k++] = 2;
  if (v <= 0xffffffffULL) ws[k++] = 4;
  ws[k++] = 8;
  return ws[rng_below(k)];
}
static size_t emit_uint_w(uint8_t *b, size_t o, uint64_t v, unsigned w) {
  return emit_head_w(b, o, 0, v, w);
}
static size_t emit_bytes(uint8_t *b, size_t o, const uint8_t *p, size_t n) {
  o = emit_head(b, o, 2, n);
  memcpy(b + o, p, n);
  return o + n;
}
#endif
