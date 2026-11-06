/* Differential tests of the verified sort-based and hash-based duplicate
 * key checks (cbor_nondet_parse_bounded_sort, cbor_nondet_parse_bounded_hash
 * with several keys, and the cbor_nondet_parse_bounded_hash_random wrapper)
 * against the verified reference (cbor_nondet_parse_bounded), on
 * hand-written cases and on random
 * equivalence-heavy inputs (tiny value domains, non-minimal integer
 * encodings, shuffled map entries, planted re-encoded duplicate keys).
 * Every call runs on heap scratch spaces of exactly the minimal size
 * (3 * N * D for sort; 3 * N * D + N and N for hash) so that
 * AddressSanitizer catches overruns; one element less must be rejected. malloc & co. are wrapped at link time and abort if called
 * during a check.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include "CBORNondet.h"
#include "CBORNondetHashRandom.h"
#include "gen.h"

static int forbid_alloc = 0;
void *__real_malloc(size_t); void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t); void __real_free(void *);
static void trap(const char *f) {
  fprintf(stderr, "FAIL: %s called during a check\n", f);
  abort();
}
void *__wrap_malloc(size_t n) { if (forbid_alloc) trap("malloc"); return __real_malloc(n); }
void *__wrap_calloc(size_t a, size_t n) { if (forbid_alloc) trap("calloc"); return __real_calloc(a, n); }
void *__wrap_realloc(void *p, size_t n) { if (forbid_alloc) trap("realloc"); return __real_realloc(p, n); }
void __wrap_free(void *p) { if (forbid_alloc) trap("free"); __real_free(p); }

static unsigned failures = 0;
#define CHECK(c, ...) do { if (!(c)) { failures++; \
  fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); \
  fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); } } while (0)

/* Returns the number of bytes consumed, 0 on failure. */
static size_t ref(size_t D, size_t N, uint8_t *b, size_t len) {
  uint8_t *p = b; size_t l = len; cbor_raw dest;
  forbid_alloc = 1;
  bool r = cbor_nondet_parse_bounded(D, N, &p, &l, &dest);
  forbid_alloc = 0;
  return r ? len - l : 0;
}

static size_t sorted(size_t D, size_t N, uint8_t *b, size_t len,
                     size_t *scratch, size_t slen) {
  uint8_t *p = b; size_t l = len; cbor_raw dest;
  forbid_alloc = 1;
  bool r = cbor_nondet_parse_bounded_sort(D, N, scratch, slen, &p, &l, &dest);
  forbid_alloc = 0;
  CHECK(r == (l < len), "inconsistent result");
  return r ? len - l : 0;
}

static size_t hashed(size_t D, size_t N, uint64_t k0, uint64_t k1, int rnd,
                     uint8_t *b, size_t len, size_t *scratch, size_t slen,
                     uint64_t *hs, size_t hlen) {
  uint8_t *p = b; size_t l = len; cbor_raw dest;
  forbid_alloc = 1;
  bool r = rnd ? cbor_nondet_parse_bounded_hash_random(D, N, scratch, slen, hs,
                                                       hlen, &p, &l, &dest)
               : cbor_nondet_parse_bounded_hash(D, N, k0, k1, scratch, slen,
                                                hs, hlen, &p, &l, &dest);
  forbid_alloc = 0;
  CHECK(r == (l < len), "inconsistent result");
  return r ? len - l : 0;
}

/* Hash keys: all-zero, the SipHash test vector key, and a random one. */
static uint64_t hkeys[3][2] = {
  { 0, 0 }, { 0x0706050403020100ULL, 0x0f0e0d0c0b0a0908ULL }, { 0, 0 }
};

/* Runs all variants and checks that they agree; returns the common result. */
static size_t run(size_t D, size_t N, uint8_t *b, size_t len) {
  size_t slen = 3 * N * D;
  CHECK(cbor_nondet_bounded_sort_scratch_ok(D, N, slen), "scratch_ok exact");
  size_t *s = malloc((slen ? slen : 1) * sizeof(size_t));
  size_t r0 = ref(D, N, b, len);
  size_t r1 = sorted(D, N, b, len, s, slen);
  CHECK(r0 == r1, "mismatch: bounded=%zu sort=%zu (D=%zu N=%zu len=%zu)",
        r0, r1, D, N, len);
  if (slen > 0) {
    CHECK(!cbor_nondet_bounded_sort_scratch_ok(D, N, slen - 1), "scratch_ok - 1");
    CHECK(sorted(D, N, b, len, s, slen - 1) == 0, "scratch - 1 accepted");
  }
  free(s);
  size_t hslen = 3 * N * D + N, hhlen = N;
  CHECK(cbor_nondet_bounded_hash_scratch_ok(D, N, hslen, hhlen), "hash scratch_ok exact");
  s = malloc((hslen ? hslen : 1) * sizeof(size_t));
  uint64_t *h = malloc((hhlen ? hhlen : 1) * sizeof(uint64_t));
  for (int k = 0; k < 4; k++) {
    size_t r2 = hashed(D, N, hkeys[k < 3 ? k : 0][0], hkeys[k < 3 ? k : 0][1],
                       k == 3, b, len, s, hslen, h, hhlen);
    CHECK(r0 == r2, "mismatch: bounded=%zu hash[%d]=%zu (D=%zu N=%zu len=%zu)",
          r0, k, r2, D, N, len);
  }
  if (hslen > 0) {
    CHECK(!cbor_nondet_bounded_hash_scratch_ok(D, N, hslen - 1, hhlen), "hash scratch_ok - 1");
    CHECK(hashed(D, N, 1, 2, 0, b, len, s, hslen - 1, h, hhlen) == 0, "hash scratch - 1 accepted");
  }
  if (hhlen > 0) {
    CHECK(!cbor_nondet_bounded_hash_scratch_ok(D, N, hslen, hhlen - 1), "hash hscratch_ok - 1");
    CHECK(hashed(D, N, 1, 2, 0, b, len, s, hslen, h, hhlen - 1) == 0, "hash hscratch - 1 accepted");
  }
  free(s); free(h);
  return r1;
}

static void test_scratch_ok(void) {
  size_t M = (size_t)-1;
  CHECK(cbor_nondet_bounded_sort_scratch_ok(0, M, 0), "D = 0");
  CHECK(!cbor_nondet_bounded_sort_scratch_ok(M, M, M), "overflow");
  CHECK(!cbor_nondet_bounded_sort_scratch_ok(2, M / 4, M), "overflow 2");
  CHECK(cbor_nondet_bounded_sort_scratch_ok(1, M / 3, M), "max");
  /* NULL scratch is rejected */
  uint8_t b[1] = { 0 }; uint8_t *p = b; size_t l = 1; cbor_raw dest;
  CHECK(!cbor_nondet_parse_bounded_sort(0, 0, NULL, 0, &p, &l, &dest), "NULL");
  CHECK(cbor_nondet_bounded_hash_scratch_ok(0, M, M, M), "hash D = 0");
  CHECK(!cbor_nondet_bounded_hash_scratch_ok(0, M, M, M - 1), "hash D = 0, hs");
  CHECK(!cbor_nondet_bounded_hash_scratch_ok(M, M, M, M), "hash overflow");
  CHECK(!cbor_nondet_bounded_hash_scratch_ok(1, M / 4 + 1, M, M), "hash overflow 2");
  CHECK(cbor_nondet_bounded_hash_scratch_ok(1, M / 4, M, M), "hash max");
  size_t sc[1]; uint64_t hs[1];
  CHECK(!cbor_nondet_parse_bounded_hash(0, 0, 0, 0, NULL, 0, hs, 0, &p, &l, &dest), "hash NULL 1");
  CHECK(!cbor_nondet_parse_bounded_hash(0, 0, 0, 0, sc, 0, NULL, 0, &p, &l, &dest), "hash NULL 2");
  CHECK(!cbor_nondet_parse_bounded_hash_random(0, 0, sc, 0, NULL, 0, &p, &l, &dest), "hash NULL 3");
  CHECK(cbor_nondet_parse_bounded_hash(0, 0, 0, 0, sc, 0, hs, 0, &p, &l, &dest), "hash D = 0 ok");
}

static void test_cases(void) {
  uint8_t b[256]; size_t o;
#define CASE(nm, ok, d, n) do { size_t r = run(d, n, b, o); \
    CHECK((r == o) == (ok), "%s: got %zu, len %zu", nm, r, o); } while (0)
  o = emit_head(b, 0, 5, 2); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  o = emit_head_w(b, o, 0, 1, 8); o = emit_head(b, o, 0, 0);
  CASE("int-noncanon-dup", false, 1, 2);
  o = emit_head(b, 0, 5, 2); o = emit_head(b, o, 0, 0); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 1, 0); o = emit_head(b, o, 0, 0);
  CASE("int-sign-distinct", true, 1, 2);
  o = emit_head(b, 0, 5, 2);
  o = emit_head(b, o, 5, 2); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 2);
  o = emit_head(b, o, 0, 3); o = emit_head(b, o, 0, 4); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 5, 2); o = emit_head(b, o, 0, 3); o = emit_head(b, o, 0, 4);
  o = emit_head(b, o, 0, 1); o = emit_head_w(b, o, 0, 2, 2); o = emit_head(b, o, 0, 0);
  CASE("map-key-permuted-dup", false, 2, 2);
  CASE("map-key-depth-bound", false, 1, 2);
  CASE("map-key-length-bound", false, 2, 1);
  o = emit_head(b, 0, 5, 2);
  o = emit_head(b, o, 5, 1); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 2);
  o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 5, 1); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 3);
  o = emit_head(b, o, 0, 0);
  CASE("map-key-distinct-values", true, 2, 2);
  o = emit_head(b, 0, 5, 2); o = emit_head(b, o, 5, 0); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 5, 0); o = emit_head(b, o, 0, 1);
  CASE("empty-map-key-dup", false, 2, 2);
  o = emit_head(b, 0, 4, 1); o = emit_head(b, o, 5, 2);
  o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  CASE("dup-under-array", false, 1, 2);
  o = emit_head(b, 0, 5, 1); o = emit_head(b, o, 0, 0); o = emit_head(b, o, 5, 2);
  o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  CASE("dup-in-value", false, 2, 2);
  o = emit_head(b, 0, 5, 2);
  for (int i = 0; i < 2; i++) {
    o = emit_head(b, o, 4, 2); o = emit_head(b, o, 5, 2);
    o = emit_head(b, o, 0, (uint64_t)(1 + i)); o = emit_head(b, o, 0, 0);
    o = emit_head(b, o, 0, (uint64_t)(2 - i)); o = emit_head(b, o, 0, 0);
    o = emit_bytes(b, o, (const uint8_t *)"a", 1); o = emit_head(b, o, 0, (uint64_t)i);
  }
  CASE("array-of-map-key-dup", false, 2, 2);
  o = emit_head(b, 0, 5, 2); o = emit_head(b, o, 6, 6); o = emit_head(b, o, 0, 1);
  o = emit_head(b, o, 0, 0); o = emit_head_w(b, o, 6, 6, 4);
  o = emit_head_w(b, o, 0, 1, 2); o = emit_head(b, o, 0, 0);
  CASE("tag-noncanon-dup", false, 1, 2);
  o = emit_head(b, 0, 0, 5);
  CASE("scalar-D0", true, 0, 0);
  o = emit_head(b, 0, 5, 0);
  CASE("map-D0", false, 0, 0);
  /* trailing bytes are not consumed */
  o = emit_head(b, 0, 5, 1); o = emit_head(b, o, 0, 1); o = emit_head(b, o, 0, 0);
  b[o] = 0;
  { size_t r = run(1, 1, b, o + 1); CHECK(r == o, "trailing: %zu", r); }
#undef CASE
}

typedef struct node {
  uint8_t maj;
  uint64_t v;
  struct node **c;
  uint8_t s[3];
} node;

#define ARENA 200000
static node arena[ARENA];
static node *ptrs[4 * ARENA];
static size_t na, np;

static node *gen_node(int depth) {
  if (na >= ARENA || np + 16 >= 4 * ARENA) depth = 0;
  node *x = &arena[na++];
  unsigned r = (unsigned)rng_below(depth > 0 ? 12 : 5);
  switch (r) {
  case 0: x->maj = 0; x->v = rng_below(8) == 0 ? (1ULL << 40) : rng_below(3); break;
  case 1: x->maj = 1; x->v = rng_below(2); break;
  case 2: case 3:
    x->maj = (uint8_t)r; x->v = rng_below(3);
    for (unsigned i = 0; i < x->v; i++) x->s[i] = (uint8_t)('a' + rng_below(2));
    break;
  case 4: x->maj = 7; x->v = 20 + rng_below(2); break;
  case 5: case 6: {
    x->maj = 4; x->v = rng_below(4);
    x->c = &ptrs[np]; np += x->v;
    for (unsigned i = 0; i < x->v; i++) x->c[i] = gen_node(depth - 1);
    break;
  }
  case 7: case 8: case 9: case 10: {
    x->maj = 5; x->v = rng_below(5);
    x->c = &ptrs[np]; np += 2 * x->v;
    for (unsigned i = 0; i < x->v; i++) {
      x->c[2 * i] = gen_node(depth - 1);
      x->c[2 * i + 1] = gen_node(depth - 1);
    }
    if (x->v >= 2 && rng_below(3) == 0) {
      unsigned i = (unsigned)rng_below(x->v), j = (unsigned)rng_below(x->v);
      if (i != j) x->c[2 * j] = x->c[2 * i];
    }
    break;
  }
  default:
    x->maj = 6; x->v = rng_below(2);
    x->c = &ptrs[np]; np += 1;
    x->c[0] = gen_node(depth - 1);
  }
  return x;
}

static size_t ser(const node *x, uint8_t *b, size_t o) {
  o = emit_head_w(b, o, x->maj, x->v, rand_width(x->v));
  switch (x->maj) {
  case 2: case 3: memcpy(b + o, x->s, x->v); o += x->v; break;
  case 4: for (uint64_t i = 0; i < x->v; i++) o = ser(x->c[i], b, o); break;
  case 6: o = ser(x->c[0], b, o); break;
  case 5: {
    unsigned perm[8];
    for (unsigned i = 0; i < x->v; i++) perm[i] = i;
    for (unsigned i = (unsigned)x->v; i > 1; i--) {
      unsigned j = (unsigned)rng_below(i), t = perm[i - 1];
      perm[i - 1] = perm[j]; perm[j] = t;
    }
    for (unsigned i = 0; i < x->v; i++) {
      o = ser(x->c[2 * perm[i]], b, o);
      o = ser(x->c[2 * perm[i] + 1], b, o);
    }
    break;
  }
  default: break;
  }
  return o;
}

static void test_random(unsigned iters) {
  static uint8_t b[1 << 16];
  unsigned acc_small = 0, acc_big = 0;
  size_t total = 0, max_len = 0;
  for (unsigned it = 0; it < iters; it++) {
    na = np = 0;
    node *x = gen_node(1 + (int)rng_below(5));
    size_t len = ser(x, b, 0);
    if (len > sizeof(b) / 2) continue;
    total += len; if (len > max_len) max_len = len;
    size_t D = rng_below(5), N = rng_below(6);
    acc_small += run(D, N, b, len) == len;
    acc_big += run(8, 8, b, len) == len;
  }
  printf("random: %u iterations, avg len %zu, max len %zu; accepted: "
         "small bounds %u, D=N=8 %u\n", iters, total / (iters ? iters : 1),
         max_len, acc_small, acc_big);
}

int main(int argc, char **argv) {
  unsigned iters = argc > 1 ? (unsigned)atoi(argv[1]) : 100000;
  CHECK(cbor_nondet_hash_random_key(hkeys[2]), "random key");
  test_scratch_ok();
  test_cases();
  test_random(iters);
  if (failures) { printf("%u FAILURES\n", failures); return 1; }
  printf("all tests passed\n");
  return 0;
}
