/* EverCBOR benchmark and conformance tests for the C API.
 *
 * This file is compiled twice:
 *   - once with -DEVERCBOR_DET, against the deterministic-encoding snapshot;
 *   - once with -DEVERCBOR_NONDET, against the non-deterministic snapshot.
 *
 * Each test is repeated BENCH_ITERATIONS times and timed.
 */

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>
#include <time.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/types.h>

#if defined(EVERCBOR_DET) && defined(EVERCBOR_NONDET)
#  error "Define exactly one of EVERCBOR_DET or EVERCBOR_NONDET"
#endif
#if !defined(EVERCBOR_DET) && !defined(EVERCBOR_NONDET)
#  error "Define exactly one of EVERCBOR_DET or EVERCBOR_NONDET"
#endif

#ifdef EVERCBOR_DET
#  include "CBORDet.h"
#  define API_NAME "det"
#  define IS_DETERMINISTIC 1
#else
#  include "CBORNondet.h"
#  define API_NAME "nondet"
#  define IS_DETERMINISTIC 0
#endif

#ifndef BENCH_ITERATIONS
#  define BENCH_ITERATIONS 1000
#endif

typedef cbor_raw cbor_t;
typedef cbor_map_entry cbor_entry_t;

/* ============================================================
 *   API wrappers: uniform surface over det / nondet.
 * ============================================================ */

/* Validate. Returns 0 on failure, length of valid prefix on success. */
static size_t cbor_v_validate(uint8_t *bytes, size_t len) {
#ifdef EVERCBOR_DET
  return cbor_det_validate(bytes, len);
#else
  uint8_t *p = bytes;
  size_t l = len;
  cbor_t dest;
  if (!cbor_nondet_parse(false, 0, &p, &l, &dest)) return 0;
  return len - l;
#endif
}

/* Parse a previously-validated buffer. Asserts on failure. */
static cbor_t cbor_v_parse(uint8_t *bytes, size_t len) {
#ifdef EVERCBOR_DET
  return cbor_det_parse(bytes, len);
#else
  uint8_t *p = bytes;
  size_t l = len;
  cbor_t dest;
  bool ok = cbor_nondet_parse(false, 0, &p, &l, &dest);
  assert(ok);
  (void)ok;
  return dest;
#endif
}

/* Serialize. Returns 0 on failure, byte count on success. */
static size_t cbor_v_serialize(cbor_t c, uint8_t *out, size_t out_len) {
#ifdef EVERCBOR_DET
  return cbor_det_serialize_safe(c, out, out_len);
#else
  return cbor_nondet_serialize(c, out, out_len);
#endif
}

static bool cbor_v_equal(cbor_t a, cbor_t b) {
#ifdef EVERCBOR_DET
  return cbor_det_equal(a, b);
#else
  return cbor_nondet_equal(a, b);
#endif
}

static uint8_t cbor_v_major_type(cbor_t c) {
#ifdef EVERCBOR_DET
  return cbor_det_major_type(c);
#else
  return cbor_nondet_major_type(c);
#endif
}

static cbor_t cbor_v_mk_uint64(uint64_t v) {
#ifdef EVERCBOR_DET
  return cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, v);
#else
  return cbor_nondet_mk_uint64(v);
#endif
}

static cbor_t cbor_v_mk_neg_int64(uint64_t v) {
#ifdef EVERCBOR_DET
  return cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, v);
#else
  return cbor_nondet_mk_neg_int64(v);
#endif
}

static bool cbor_v_mk_byte_string(uint8_t *bytes, uint64_t len, cbor_t *dest) {
#ifdef EVERCBOR_DET
  return cbor_det_mk_byte_string_from_arrayptr(bytes, len, dest);
#else
  return cbor_nondet_mk_byte_string(bytes, len, dest);
#endif
}

static bool cbor_v_mk_text_string(uint8_t *bytes, uint64_t len, cbor_t *dest) {
#ifdef EVERCBOR_DET
  return cbor_det_mk_text_string_from_arrayptr(bytes, len, dest);
#else
  return cbor_nondet_mk_text_string(bytes, len, dest);
#endif
}

static bool cbor_v_mk_array(cbor_t *items, uint64_t len, cbor_t *dest) {
#ifdef EVERCBOR_DET
  *dest = cbor_det_mk_array_from_array(items, len);
  return true;
#else
  return cbor_nondet_mk_array(items, len, dest);
#endif
}

static cbor_entry_t cbor_v_mk_map_entry(cbor_t k, cbor_t v) {
#ifdef EVERCBOR_DET
  return cbor_det_mk_map_entry(k, v);
#else
  return cbor_nondet_mk_map_entry(k, v);
#endif
}

/* Construct a map from a (mutable) array of entries. The underlying API may
   re-sort the entries in place to canonical order. */
static bool cbor_v_mk_map(cbor_entry_t *entries, uint64_t len, cbor_t *dest) {
#ifdef EVERCBOR_DET
  return cbor_det_mk_map_from_array_safe(entries, len, dest);
#else
  return cbor_nondet_mk_map(entries, len, dest);
#endif
}

static bool cbor_v_mk_tagged(uint64_t tag, cbor_t *payload, cbor_t *dest) {
#ifdef EVERCBOR_DET
  *dest = cbor_det_mk_tagged(tag, payload);
  return true;
#else
  return cbor_nondet_mk_tagged(tag, payload, dest);
#endif
}

static bool cbor_v_mk_simple_value(uint8_t v, cbor_t *dest) {
#ifdef EVERCBOR_DET
  *dest = cbor_det_mk_simple_value(v);
  return true;
#else
  return cbor_nondet_mk_simple_value(v, dest);
#endif
}

static bool cbor_v_read_uint64(cbor_t c, uint64_t *out) {
#ifdef EVERCBOR_DET
  *out = cbor_det_read_uint64(c);
  return true;
#else
  return cbor_nondet_read_uint64(c, out);
#endif
}

static bool cbor_v_read_simple_value(cbor_t c, uint8_t *out) {
#ifdef EVERCBOR_DET
  *out = cbor_det_read_simple_value(c);
  return true;
#else
  return cbor_nondet_read_simple_value(c, out);
#endif
}

static bool cbor_v_get_string(cbor_t c, uint8_t **payload, uint64_t *len) {
#ifdef EVERCBOR_DET
  *len = cbor_det_get_string_length(c);
  *payload = cbor_det_get_string(c);
  return true;
#else
  return cbor_nondet_get_string(c, payload, len);
#endif
}

static bool cbor_v_get_array_length(cbor_t c, uint64_t *out) {
#ifdef EVERCBOR_DET
  *out = cbor_det_get_array_length(c);
  return true;
#else
  return cbor_nondet_get_array_length(c, out);
#endif
}

static bool cbor_v_get_array_item(cbor_t c, uint64_t i, cbor_t *out) {
#ifdef EVERCBOR_DET
  *out = cbor_det_get_array_item(c, i);
  return true;
#else
  return cbor_nondet_get_array_item(c, i, out);
#endif
}

static bool cbor_v_get_map_length(cbor_t c, uint64_t *out) {
#ifdef EVERCBOR_DET
  *out = cbor_det_get_map_length(c);
  return true;
#else
  return cbor_nondet_get_map_length(c, out);
#endif
}

static bool cbor_v_map_get(cbor_t c, cbor_t k, cbor_t *out) {
#ifdef EVERCBOR_DET
  return cbor_det_map_get(c, k, out);
#else
  return cbor_nondet_map_get(c, k, out);
#endif
}

static bool cbor_v_get_tagged(cbor_t c, cbor_t *payload, uint64_t *tag) {
#ifdef EVERCBOR_DET
  *tag = cbor_det_get_tagged_tag(c);
  *payload = cbor_det_get_tagged_payload(c);
  return true;
#else
  return cbor_nondet_get_tagged(c, payload, tag);
#endif
}

/* ============================================================
 *   Common test helpers
 * ============================================================ */

#define SER_BUF_SIZE 4096

#define TFAIL(msg, ...) do {                                                 \
    fprintf(stderr, "  FAIL: " msg "\n", ##__VA_ARGS__);                     \
    return 1;                                                                \
  } while (0)

/* ---------- File-writing infrastructure ----------
 *
 * Each test writes its input bytes to <out_dir>/<api>_<name>.input.cbor.
 * Each valid test also writes the bytes it serialized through the API to
 *   <out_dir>/<api>_<name>.serialized.cbor
 *
 * Writes happen only on the FIRST call to each test (the "warmup" pass);
 * subsequent timed iterations skip them. This keeps the timing loop free
 * of disk I/O while still emitting one copy of each artefact.
 */

static const char *g_out_dir       = "out";
static const char *g_current_test  = "(unset)";
static int         g_write_files   = 0;

static int ensure_out_dir(void) {
  if (mkdir(g_out_dir, 0755) != 0 && errno != EEXIST) {
    fprintf(stderr, "FATAL: cannot create output dir '%s': %s\n",
            g_out_dir, strerror(errno));
    return 1;
  }
  return 0;
}

static int write_artefact(const char *suffix, uint8_t *bytes, size_t len) {
  char path[1024];
  int n = snprintf(path, sizeof(path), "%s/%s_%s.%s.cbor",
                   g_out_dir, API_NAME, g_current_test, suffix);
  if (n < 0 || (size_t)n >= sizeof(path)) {
    fprintf(stderr, "FATAL: artefact path too long for test '%s'\n",
            g_current_test);
    return 1;
  }
  FILE *f = fopen(path, "wb");
  if (!f) {
    fprintf(stderr, "FATAL: cannot open '%s' for write: %s\n",
            path, strerror(errno));
    return 1;
  }
  size_t w = fwrite(bytes, 1, len, f);
  fclose(f);
  if (w != len) {
    fprintf(stderr, "FATAL: short write to '%s' (%zu/%zu)\n", path, w, len);
    return 1;
  }
  return 0;
}

static int maybe_write_input(uint8_t *bytes, size_t len) {
  if (!g_write_files) return 0;
  return write_artefact("input", bytes, len);
}

static int maybe_write_serialized(uint8_t *bytes, size_t len) {
  if (!g_write_files) return 0;
  return write_artefact("serialized", bytes, len);
}

/* For valid encodings: validate, parse, compare with `expected`,
 * serialize `expected`, validate+parse the output, compare again.
 * If `match_bytes`, also assert the serialized output equals `bytes`.
 */
static int do_run_valid(uint8_t *bytes, size_t len, cbor_t expected,
                        bool match_bytes) {
  /* Persist input bytes to disk for cross-language test consumers. */
  if (maybe_write_input(bytes, len)) return 1;

  /* (b) Validate. */
  size_t vsize = cbor_v_validate(bytes, len);
  if (vsize == 0) TFAIL("validation rejected a valid encoding");
  if (vsize != len) TFAIL("validation consumed %zu of %zu bytes", vsize, len);

  /* (c) Parse, then check accessor equality. */
  cbor_t parsed = cbor_v_parse(bytes, vsize);
  if (!cbor_v_equal(parsed, expected))
    TFAIL("parsed value not equal to constructed expected");
  if (!cbor_v_equal(expected, parsed))
    TFAIL("equality is not symmetric");

  /* (e) Serialize the constructed (independent) value. */
  static uint8_t out[SER_BUF_SIZE];
  size_t outlen = cbor_v_serialize(expected, out, SER_BUF_SIZE);
  if (outlen == 0) TFAIL("serialization failed");
  if (maybe_write_serialized(out, outlen)) return 1;

  /* (f) Round-trip: validate and parse the serialized output. */
  size_t vsize2 = cbor_v_validate(out, outlen);
  if (vsize2 != outlen) TFAIL("round-trip validation mismatch (%zu/%zu)",
                              vsize2, outlen);
  cbor_t reparsed = cbor_v_parse(out, vsize2);
  if (!cbor_v_equal(reparsed, expected))
    TFAIL("round-trip equality failed");

  /* (g) Deterministic-only: serialized bytes must equal input bytes. */
  if (match_bytes) {
    if (outlen != len) TFAIL("byte length mismatch (orig=%zu, ser=%zu)",
                             len, outlen);
    if (memcmp(bytes, out, len) != 0)
      TFAIL("byte content mismatch under deterministic encoding");
  }
  return 0;
}

/* For valid encodings whose canonical form may differ from `bytes`. */
#if !IS_DETERMINISTIC
static int run_valid_no_match(uint8_t *bytes, size_t len, cbor_t expected) {
  return do_run_valid(bytes, len, expected, false);
}
#endif

/* For valid canonical encodings (det only requires byte equality on output). */
static int run_valid_match(uint8_t *bytes, size_t len, cbor_t expected) {
  return do_run_valid(bytes, len, expected, IS_DETERMINISTIC);
}

/* For invalid encodings (validation must reject). */
static int run_invalid(uint8_t *bytes, size_t len) {
  if (maybe_write_input(bytes, len)) return 1;
  size_t vsize = cbor_v_validate(bytes, len);
  if (vsize != 0)
    TFAIL("validation accepted an invalid encoding (vsize=%zu)", vsize);
  return 0;
}

/* ============================================================
 *   Test cases.
 *
 *   Naming convention:
 *     test_<scenario>_canonical  : canonical encoding (valid in both APIs).
 *     test_<scenario>_nondet     : non-canonical but well-formed encoding
 *                                  (valid in nondet only; rejected by det).
 *     test_<scenario>_invalid    : malformed encoding (rejected by both).
 * ============================================================ */

/* ---------- Major type 0: unsigned integer ---------- */

static int test_uint_zero_canonical(void) {
  uint8_t bytes[] = { 0x00 };
  cbor_t expected = cbor_v_mk_uint64(0);
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_UINT64) TFAIL("major type");
  uint64_t v;
  if (!cbor_v_read_uint64(expected, &v) || v != 0) TFAIL("read");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_small_canonical(void) {
  uint8_t bytes[] = { 0x17 }; /* 23, last value in short form */
  cbor_t expected = cbor_v_mk_uint64(23);
  uint64_t v;
  if (!cbor_v_read_uint64(expected, &v) || v != 23) TFAIL("read");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_one_byte_canonical(void) {
  uint8_t bytes[] = { 0x18, 0x64 }; /* 100 */
  cbor_t expected = cbor_v_mk_uint64(100);
  uint64_t v;
  if (!cbor_v_read_uint64(expected, &v) || v != 100) TFAIL("read");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_two_byte_canonical(void) {
  uint8_t bytes[] = { 0x19, 0x03, 0xe8 }; /* 1000 */
  cbor_t expected = cbor_v_mk_uint64(1000);
  uint64_t v;
  if (!cbor_v_read_uint64(expected, &v) || v != 1000) TFAIL("read");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_four_byte_canonical(void) {
  uint8_t bytes[] = { 0x1a, 0x00, 0x0f, 0x42, 0x40 }; /* 1000000 */
  cbor_t expected = cbor_v_mk_uint64(1000000);
  uint64_t v;
  if (!cbor_v_read_uint64(expected, &v) || v != 1000000) TFAIL("read");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_eight_byte_canonical(void) {
  uint8_t bytes[] = { 0x1b, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00 };
  cbor_t expected = cbor_v_mk_uint64((uint64_t)1 << 32);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* Non-canonical: zero with 1-byte argument. Valid in nondet, rejected by det. */
static int test_uint_zero_nondet(void) {
  uint8_t bytes[] = { 0x18, 0x00 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t expected = cbor_v_mk_uint64(0);
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* Non-canonical: 100 with 2-byte argument. */
static int test_uint_100_nondet(void) {
  uint8_t bytes[] = { 0x19, 0x00, 0x64 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t expected = cbor_v_mk_uint64(100);
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* Non-canonical: 0 with 8-byte argument. */
static int test_uint_zero_long_nondet(void) {
  uint8_t bytes[] = { 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t expected = cbor_v_mk_uint64(0);
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* ---------- Major type 1: negative integer ---------- */

static int test_neg_minus_one_canonical(void) {
  uint8_t bytes[] = { 0x20 }; /* -1 */
  cbor_t expected = cbor_v_mk_neg_int64(0);
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_NEG_INT64)
    TFAIL("major type");
  uint64_t v;
  if (!cbor_v_read_uint64(expected, &v) || v != 0) TFAIL("read");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_neg_small_canonical(void) {
  uint8_t bytes[] = { 0x29 }; /* -10 */
  cbor_t expected = cbor_v_mk_neg_int64(9);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_neg_one_byte_canonical(void) {
  uint8_t bytes[] = { 0x38, 0x63 }; /* -100 */
  cbor_t expected = cbor_v_mk_neg_int64(99);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_neg_minus_one_nondet(void) {
  uint8_t bytes[] = { 0x38, 0x00 }; /* -1 with 1-byte arg */
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t expected = cbor_v_mk_neg_int64(0);
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* ---------- Major type 2: byte string ---------- */

static int test_bstr_empty_canonical(void) {
  uint8_t bytes[] = { 0x40 };
  uint8_t payload[] = { 0 }; /* unused but distinct allocation */
  (void)payload;
  cbor_t expected;
  if (!cbor_v_mk_byte_string(payload, 0, &expected))
    TFAIL("mk byte string");
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_BYTE_STRING)
    TFAIL("major type");
  uint8_t *p; uint64_t l;
  if (!cbor_v_get_string(expected, &p, &l)) TFAIL("get string");
  if (l != 0) TFAIL("len");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_bstr_short_canonical(void) {
  uint8_t bytes[] = { 0x44, 0xde, 0xad, 0xbe, 0xef };
  /* Constructor uses an INDEPENDENT, separately-allocated buffer. */
  static uint8_t payload[] = { 0xde, 0xad, 0xbe, 0xef };
  cbor_t expected;
  if (!cbor_v_mk_byte_string(payload, sizeof(payload), &expected))
    TFAIL("mk byte string");
  uint8_t *p; uint64_t l;
  if (!cbor_v_get_string(expected, &p, &l)) TFAIL("get string");
  if (l != 4 || memcmp(p, payload, 4) != 0) TFAIL("contents");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_bstr_empty_nondet(void) {
  uint8_t bytes[] = { 0x58, 0x00 }; /* empty bstr with 1-byte length arg */
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  static uint8_t payload[] = { 0 };
  cbor_t expected;
  if (!cbor_v_mk_byte_string(payload, 0, &expected))
    TFAIL("mk byte string");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* ---------- Major type 3: text string ---------- */

static int test_tstr_empty_canonical(void) {
  uint8_t bytes[] = { 0x60 };
  static uint8_t payload[] = { 0 };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, 0, &expected))
    TFAIL("mk text string");
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_TEXT_STRING)
    TFAIL("major type");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tstr_hello_canonical(void) {
  uint8_t bytes[] = { 0x65, 'h', 'e', 'l', 'l', 'o' };
  static uint8_t payload[] = { 'h', 'e', 'l', 'l', 'o' };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, sizeof(payload), &expected))
    TFAIL("mk text string");
  uint8_t *p; uint64_t l;
  if (!cbor_v_get_string(expected, &p, &l)) TFAIL("get string");
  if (l != 5 || memcmp(p, payload, 5) != 0) TFAIL("contents");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tstr_hello_nondet(void) {
  uint8_t bytes[] = { 0x78, 0x05, 'h', 'e', 'l', 'l', 'o' };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  static uint8_t payload[] = { 'h', 'e', 'l', 'l', 'o' };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, sizeof(payload), &expected))
    TFAIL("mk text string");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* ---------- Major type 4: array ---------- */

static int test_arr_empty_canonical(void) {
  uint8_t bytes[] = { 0x80 };
  cbor_t items[1] = { cbor_v_mk_uint64(0) }; /* unused */
  cbor_t expected;
  if (!cbor_v_mk_array(items, 0, &expected)) TFAIL("mk array");
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_ARRAY) TFAIL("major");
  uint64_t l;
  if (!cbor_v_get_array_length(expected, &l)) TFAIL("array length");
  if (l != 0) TFAIL("array length value");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_arr_three_canonical(void) {
  uint8_t bytes[] = { 0x83, 0x01, 0x02, 0x03 };
  cbor_t items[3] = { cbor_v_mk_uint64(1),
                      cbor_v_mk_uint64(2),
                      cbor_v_mk_uint64(3) };
  cbor_t expected;
  if (!cbor_v_mk_array(items, 3, &expected)) TFAIL("mk array");
  uint64_t l;
  if (!cbor_v_get_array_length(expected, &l) || l != 3) TFAIL("len");
  cbor_t item;
  uint64_t v;
  if (!cbor_v_get_array_item(expected, 0, &item)) TFAIL("get item 0");
  if (!cbor_v_read_uint64(item, &v) || v != 1) TFAIL("item 0 value");
  if (!cbor_v_get_array_item(expected, 2, &item)) TFAIL("get item 2");
  if (!cbor_v_read_uint64(item, &v) || v != 3) TFAIL("item 2 value");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_arr_empty_nondet(void) {
  uint8_t bytes[] = { 0x98, 0x00 }; /* empty array with 1-byte length arg */
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t items[1] = { cbor_v_mk_uint64(0) };
  cbor_t expected;
  if (!cbor_v_mk_array(items, 0, &expected)) TFAIL("mk array");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* Deeply nested array: [[[...[1]...]]] of depth ARR_DEPTH. */
#define ARR_DEPTH 30
static int test_arr_deeply_nested_canonical(void) {
  /* Canonical bytes: ARR_DEPTH copies of 0x81 followed by 0x01. */
  static uint8_t bytes[ARR_DEPTH + 1];
  static int initialized = 0;
  if (!initialized) {
    for (int i = 0; i < ARR_DEPTH; i++) bytes[i] = 0x81;
    bytes[ARR_DEPTH] = 0x01;
    initialized = 1;
  }
  cbor_t levels[ARR_DEPTH + 1];
  levels[0] = cbor_v_mk_uint64(1);
  for (int i = 1; i <= ARR_DEPTH; i++) {
    if (!cbor_v_mk_array(&levels[i - 1], 1, &levels[i])) TFAIL("mk array");
  }
  return run_valid_match(bytes, sizeof(bytes), levels[ARR_DEPTH]);
}

/* ---------- Major type 5: map ---------- */

static int test_map_empty_canonical(void) {
  uint8_t bytes[] = { 0xa0 };
  cbor_entry_t entries[1] = { cbor_v_mk_map_entry(cbor_v_mk_uint64(0),
                                                  cbor_v_mk_uint64(0)) };
  cbor_t expected;
  if (!cbor_v_mk_map(entries, 0, &expected)) TFAIL("mk map");
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_MAP) TFAIL("major");
  uint64_t l;
  if (!cbor_v_get_map_length(expected, &l) || l != 0) TFAIL("len");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* {1: 0x01, 2: "ab"} - canonical: keys sorted by length-then-lex.
 * Canonical encoding: a2 01 41 01 02 62 61 62 */
static int test_map_two_canonical(void) {
  uint8_t bytes[] = {
    0xa2,
    0x01, 0x41, 0x01,                /* key 1 -> bstr [0x01] */
    0x02, 0x62, 0x61, 0x62           /* key 2 -> tstr "ab" */
  };
  static uint8_t bs[] = { 0x01 };
  static uint8_t ts[] = { 'a', 'b' };
  cbor_t k1 = cbor_v_mk_uint64(1);
  cbor_t k2 = cbor_v_mk_uint64(2);
  cbor_t v1, v2;
  if (!cbor_v_mk_byte_string(bs, sizeof(bs), &v1)) TFAIL("mk bstr");
  if (!cbor_v_mk_text_string(ts, sizeof(ts), &v2)) TFAIL("mk tstr");
  cbor_entry_t entries[2] = {
    cbor_v_mk_map_entry(k1, v1),
    cbor_v_mk_map_entry(k2, v2)
  };
  cbor_t expected;
  if (!cbor_v_mk_map(entries, 2, &expected)) TFAIL("mk map");

  /* Accessor checks: lookup */
  cbor_t found;
  if (!cbor_v_map_get(expected, k1, &found)) TFAIL("map_get(1)");
  if (cbor_v_major_type(found) != CBOR_MAJOR_TYPE_BYTE_STRING)
    TFAIL("k1 value type");
  if (!cbor_v_map_get(expected, k2, &found)) TFAIL("map_get(2)");
  if (cbor_v_major_type(found) != CBOR_MAJOR_TYPE_TEXT_STRING)
    TFAIL("k2 value type");
  cbor_t k3 = cbor_v_mk_uint64(99);
  if (cbor_v_map_get(expected, k3, &found)) TFAIL("map_get(99) succeeded");

  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* Same map but with keys in reverse order in the input bytes.
   Det: invalid (out-of-order keys). Nondet: valid, but byte-mismatch on round-trip. */
static int test_map_two_nondet(void) {
  uint8_t bytes[] = {
    0xa2,
    0x02, 0x62, 0x61, 0x62,
    0x01, 0x41, 0x01
  };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  static uint8_t bs[] = { 0x01 };
  static uint8_t ts[] = { 'a', 'b' };
  cbor_t k1 = cbor_v_mk_uint64(1);
  cbor_t k2 = cbor_v_mk_uint64(2);
  cbor_t v1, v2;
  if (!cbor_v_mk_byte_string(bs, sizeof(bs), &v1)) TFAIL("mk bstr");
  if (!cbor_v_mk_text_string(ts, sizeof(ts), &v2)) TFAIL("mk tstr");
  /* Construct in canonical order; the parsed-from-bytes object will compare
     equal regardless of key order. */
  cbor_entry_t entries[2] = {
    cbor_v_mk_map_entry(k1, v1),
    cbor_v_mk_map_entry(k2, v2)
  };
  cbor_t expected;
  if (!cbor_v_mk_map(entries, 2, &expected)) TFAIL("mk map");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* Deeply nested map: {0: {0: {0: ... {0: 0} ... }}} of depth MAP_DEPTH.
 *
 * NOTE: the non-deterministic equality test on chained singleton maps has
 * exponential cost (it pairs each key/value of the recursion both ways),
 * so the depth is kept moderate to keep the benchmark in the second-range
 * across iterations. The depth is still large enough to exercise the
 * recursive validator and serializer paths. */
#define MAP_DEPTH 10
static int test_map_deeply_nested_canonical(void) {
  /* Canonical bytes: MAP_DEPTH copies of 0xa1 0x00 then 0x00 leaf. */
  static uint8_t bytes[2 * MAP_DEPTH + 1];
  static int initialized = 0;
  if (!initialized) {
    for (int i = 0; i < MAP_DEPTH; i++) {
      bytes[2 * i]     = 0xa1;
      bytes[2 * i + 1] = 0x00;
    }
    bytes[2 * MAP_DEPTH] = 0x00;
    initialized = 1;
  }
  cbor_t values[MAP_DEPTH + 1];
  cbor_entry_t entries[MAP_DEPTH][1];
  values[0] = cbor_v_mk_uint64(0);
  for (int i = 1; i <= MAP_DEPTH; i++) {
    cbor_t k = cbor_v_mk_uint64(0);
    entries[i - 1][0] = cbor_v_mk_map_entry(k, values[i - 1]);
    if (!cbor_v_mk_map(entries[i - 1], 1, &values[i])) TFAIL("mk map level");
  }
  return run_valid_match(bytes, sizeof(bytes), values[MAP_DEPTH]);
}

/* "Deeply nested map" (DNM) parameterized by depth d and a non-negative
 * leaf base x. Recursive definition with TWO entries at every level,
 * with the recursion living on the *key* side of both entries:
 *
 *   DNM(0, x) = uint(x)
 *   DNM(d, x) = { DNM(d-1, 2x) : 0,
 *                 DNM(d-1, 2x+1) : 1 }
 *
 * Both keys at each map level are themselves nested maps; only the
 * value parts (0 and 1) are constants. The leaves of DNM(d, x) span
 * the integer range [x * 2^d, (x+1) * 2^d). For depth 3 and x in
 * {0, 1} this covers 0..15. The canonical (length-then-lex) key
 * ordering is preserved at every level by construction: at any node,
 * the "left" key DNM(d-1, 2x) has strictly smaller leaves than the
 * "right" key DNM(d-1, 2x+1), so its canonical encoding is byte-wise
 * shorter-or-equal and lex-smaller.
 *
 * Two such DNMs are then assembled into 2-element-array "pairs" that
 * serve as the two outer-map keys.
 *
 * Depth is kept moderate because the non-deterministic equality test
 * is O(c^d) for some c > 1 on this binary-tree structure.
 */
#define MAP_KEY_DEPTH 3

/* Canonical CBOR uint encoder, sufficient for v < 2^16. */
static size_t emit_canonical_uint(uint8_t *bytes, size_t off, uint64_t v) {
  if (v < 24) {
    bytes[off++] = (uint8_t)v;
  } else if (v < 256) {
    bytes[off++] = 0x18;
    bytes[off++] = (uint8_t)v;
  } else {
    bytes[off++] = 0x19;
    bytes[off++] = (uint8_t)(v >> 8);
    bytes[off++] = (uint8_t)v;
  }
  return off;
}

/* Emit DNM(depth, leaf_base) into `bytes` at offset `off`. */
static size_t emit_dnm(uint8_t *bytes, size_t off,
                       int depth, uint64_t leaf_base) {
  if (depth == 0)
    return emit_canonical_uint(bytes, off, leaf_base);
  bytes[off++] = 0xa2; /* map of 2 entries */
  off = emit_dnm(bytes, off, depth - 1, 2 * leaf_base);
  off = emit_canonical_uint(bytes, off, 0);
  off = emit_dnm(bytes, off, depth - 1, 2 * leaf_base + 1);
  off = emit_canonical_uint(bytes, off, 1);
  return off;
}

/* Storage pools for the DNM CBOR objects. The constructed CBOR maps
 * keep slices into these arrays alive, so they must persist as long as
 * the resulting objects are used. The pools are reset (overwritten) at
 * the start of each test iteration. */
#define DNM_POOL_SIZE 256
static cbor_t       dnm_node_pool [DNM_POOL_SIZE];
static cbor_entry_t dnm_entry_pool[DNM_POOL_SIZE];
static int dnm_node_used;
static int dnm_entry_used;

static void dnm_pool_reset(void) {
  dnm_node_used  = 0;
  dnm_entry_used = 0;
}

static bool build_dnm(int depth, uint64_t leaf_base, cbor_t *out) {
  if (dnm_node_used >= DNM_POOL_SIZE) return false;
  cbor_t *slot = &dnm_node_pool[dnm_node_used++];
  if (depth == 0) {
    *slot = cbor_v_mk_uint64(leaf_base);
    *out = *slot;
    return true;
  }
  cbor_t k1, k2;
  if (!build_dnm(depth - 1, 2 * leaf_base,     &k1)) return false;
  if (!build_dnm(depth - 1, 2 * leaf_base + 1, &k2)) return false;
  if (dnm_entry_used + 2 > DNM_POOL_SIZE) return false;
  cbor_entry_t *entries = &dnm_entry_pool[dnm_entry_used];
  dnm_entry_used += 2;
  entries[0] = cbor_v_mk_map_entry(k1, cbor_v_mk_uint64(0));
  entries[1] = cbor_v_mk_map_entry(k2, cbor_v_mk_uint64(1));
  if (!cbor_v_mk_map(entries, 2, slot)) return false;
  *out = *slot;
  return true;
}

static int test_map_with_nested_map_keys_canonical(void) {
  /* Outer map with two entries; each key is a 2-element array of DNMs.
   *   key1 = [DNM(d,0), DNM(d,0)]   value 0
   *   key2 = [DNM(d,0), DNM(d,1)]   value 1
   * key1 < key2 lex-wise since both pairs match in their first element
   * and DNM(d,0) < DNM(d,1) (the latter has strictly larger leaves).
   */
  static uint8_t bytes[1024];
  static size_t  bytes_len;
  static int     initialized = 0;
  if (!initialized) {
    size_t off = 0;
    bytes[off++] = 0xa2;                      /* outer 2-entry map */

    /* Entry 1: pair1 = [DNM(d, 0), DNM(d, 0)], value 0 */
    bytes[off++] = 0x82;                      /* 2-element array */
    off = emit_dnm(bytes, off, MAP_KEY_DEPTH, 0);
    off = emit_dnm(bytes, off, MAP_KEY_DEPTH, 0);
    off = emit_canonical_uint(bytes, off, 0);

    /* Entry 2: pair2 = [DNM(d, 0), DNM(d, 1)], value 1 */
    bytes[off++] = 0x82;
    off = emit_dnm(bytes, off, MAP_KEY_DEPTH, 0);
    off = emit_dnm(bytes, off, MAP_KEY_DEPTH, 1);
    off = emit_canonical_uint(bytes, off, 1);

    bytes_len = off;
    initialized = 1;
  }

  /* Build the same value through the API. */
  dnm_pool_reset();
  cbor_t dnm_a, dnm_b;
  if (!build_dnm(MAP_KEY_DEPTH, 0, &dnm_a)) TFAIL("build dnm_a");
  if (!build_dnm(MAP_KEY_DEPTH, 1, &dnm_b)) TFAIL("build dnm_b");

  static cbor_t pair1_items[2];
  static cbor_t pair2_items[2];
  pair1_items[0] = dnm_a; pair1_items[1] = dnm_a;
  pair2_items[0] = dnm_a; pair2_items[1] = dnm_b;

  cbor_t pair1, pair2;
  if (!cbor_v_mk_array(pair1_items, 2, &pair1)) TFAIL("mk pair1");
  if (!cbor_v_mk_array(pair2_items, 2, &pair2)) TFAIL("mk pair2");

  static cbor_entry_t outer_entries[2];
  outer_entries[0] = cbor_v_mk_map_entry(pair1, cbor_v_mk_uint64(0));
  outer_entries[1] = cbor_v_mk_map_entry(pair2, cbor_v_mk_uint64(1));
  cbor_t expected;
  if (!cbor_v_mk_map(outer_entries, 2, &expected)) TFAIL("mk outer map");

  /* Accessor checks on each composite key. */
  cbor_t got;
  uint64_t v;
  if (!cbor_v_map_get(expected, pair1, &got)) TFAIL("map_get(pair1)");
  if (!cbor_v_read_uint64(got, &v) || v != 0) TFAIL("pair1 value");
  if (!cbor_v_map_get(expected, pair2, &got)) TFAIL("map_get(pair2)");
  if (!cbor_v_read_uint64(got, &v) || v != 1) TFAIL("pair2 value");

  return run_valid_match(bytes, bytes_len, expected);
}

/* Invalid: map with two equal keys (same canonical encoding). */
static int test_map_dup_key_invalid(void) {
  uint8_t bytes[] = {
    0xa2,
    0x01, 0x00,
    0x01, 0x01
  };
  return run_invalid(bytes, sizeof(bytes));
}

/* Invalid: map with two equal keys encoded differently (1 vs 0x18 0x01).
 * Both encode the integer 1; the validator must detect the duplicate
 * regardless of encoding. */
static int test_map_dup_key_diff_encoding_invalid(void) {
  uint8_t bytes[] = {
    0xa2,
    0x01, 0x00,
    0x18, 0x01, 0x01
  };
  return run_invalid(bytes, sizeof(bytes));
}

/* ---------- Major type 6: tagged ---------- */

/* Tag value 1000 (= 0x3e8) is intentionally chosen because it has no
   semantic decoder in the popular CBOR libraries (e.g. Python cbor2),
   so the value round-trips as a generic tagged item rather than being
   automatically converted to e.g. a datetime. Canonical encoding uses
   the 2-byte argument form (0xd9 0x03 0xe8); the *_nondet variant
   below uses the longer 4-byte argument form. */
static int test_tag_canonical(void) {
  uint8_t bytes[] = { 0xd9, 0x03, 0xe8, 0x00 }; /* tag 1000, payload uint 0 */
  cbor_t payload = cbor_v_mk_uint64(0);
  cbor_t expected;
  if (!cbor_v_mk_tagged(1000, &payload, &expected)) TFAIL("mk tagged");
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_TAGGED) TFAIL("major");
  cbor_t got_payload;
  uint64_t got_tag;
  if (!cbor_v_get_tagged(expected, &got_payload, &got_tag))
    TFAIL("get tagged");
  if (got_tag != 1000) TFAIL("tag value");
  uint64_t pv;
  if (!cbor_v_read_uint64(got_payload, &pv) || pv != 0) TFAIL("payload");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tag_nondet(void) {
  /* Tag 1000 with the (non-canonical) 4-byte argument form. */
  uint8_t bytes[] = { 0xda, 0x00, 0x00, 0x03, 0xe8, 0x00 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t payload = cbor_v_mk_uint64(0);
  cbor_t expected;
  if (!cbor_v_mk_tagged(1000, &payload, &expected)) TFAIL("mk tagged");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* ---------- Major type 7: simple values (no floats) ---------- */

static int test_simple_short_canonical(void) {
  uint8_t bytes[] = { 0xf0 }; /* simple value 16 */
  cbor_t expected;
  if (!cbor_v_mk_simple_value(16, &expected)) TFAIL("mk simple");
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_SIMPLE_VALUE)
    TFAIL("major");
  uint8_t v;
  if (!cbor_v_read_simple_value(expected, &v) || v != 16) TFAIL("read");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_simple_long_canonical(void) {
  uint8_t bytes[] = { 0xf8, 0x64 }; /* simple value 100, only valid form */
  cbor_t expected;
  if (!cbor_v_mk_simple_value(100, &expected)) TFAIL("mk simple");
  uint8_t v;
  if (!cbor_v_read_simple_value(expected, &v) || v != 100) TFAIL("read");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* Invalid: simple value 24 in 1-byte form (RFC 8949 §3.3 forbids
   0xf8 followed by < 0x20). */
static int test_simple_24_invalid(void) {
  uint8_t bytes[] = { 0xf8, 0x18 };
  return run_invalid(bytes, sizeof(bytes));
}

/* For simple values, every additional info < 0x20 is forbidden in 1-byte form,
   so there's no "valid in nondet only" 1-byte encoding for simple 16.
   We instead provide a "non-canonical-only" simple value test: a non-det-only
   sibling for simple 16 would be a 2-byte argument form, but additional info
   25 in major 7 means half-precision float (unsupported). So instead we
   exercise an invalid simple value <0x20 in 1-byte form here. */

/* ============================================================
 *   Tests ported from cbor-test-unverified
 * ============================================================
 *
 * The following tests are imported from the older C test suites used
 * elsewhere in the repository:
 *
 *   - src/cbor/pulse/det/c/test/CBORDetTest.c
 *   - src/cbor/pulse/nondet/c/test/CBORNondetTest.c
 *   - src/cbor/pulse/nondet/c/test/qcbortests.c
 *   - src/cbor/pulse/{det,nondet}/c/test/main.c (large_array_test)
 *
 * Tests already covered above (e.g., uint 0, uint 100, small text
 * strings, empty maps/arrays) are not duplicated. Only genuinely new
 * cases are introduced here. Each one is added as a stand-alone test
 * so it gets its own per-test artefact files and benchmark line.
 */

/* ---------- Extra integer tests from gentest ---------- */

static int test_uint_one_canonical(void) {
  uint8_t bytes[] = { 0x01 };
  cbor_t expected = cbor_v_mk_uint64(1);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_ten_canonical(void) {
  uint8_t bytes[] = { 0x0a };
  cbor_t expected = cbor_v_mk_uint64(10);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_24_canonical(void) {
  uint8_t bytes[] = { 0x18, 0x18 };
  cbor_t expected = cbor_v_mk_uint64(24);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_25_canonical(void) {
  uint8_t bytes[] = { 0x18, 0x19 };
  cbor_t expected = cbor_v_mk_uint64(25);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_uint_trillion_canonical(void) {
  /* 1_000_000_000_000 = 0xE8D4A51000 — 8-byte argument form. */
  uint8_t bytes[] = { 0x1b, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00 };
  cbor_t expected = cbor_v_mk_uint64(1000000000000ULL);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_neg_two_byte_canonical(void) {
  uint8_t bytes[] = { 0x39, 0x03, 0xe7 }; /* -1000 */
  cbor_t expected = cbor_v_mk_neg_int64(999);
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* ---------- Extra text-string tests from gentest ---------- */

static int test_tstr_a_canonical(void) {
  uint8_t bytes[] = { 0x61, 'a' };
  static uint8_t payload[] = { 'a' };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, sizeof(payload), &expected))
    TFAIL("mk text string");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tstr_ietf_canonical(void) {
  uint8_t bytes[] = { 0x64, 'I', 'E', 'T', 'F' };
  static uint8_t payload[] = { 'I', 'E', 'T', 'F' };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, sizeof(payload), &expected))
    TFAIL("mk text string");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tstr_escapes_canonical(void) {
  /* The two characters '"' and '\\'. */
  uint8_t bytes[] = { 0x62, 0x22, 0x5c };
  static uint8_t payload[] = { 0x22, 0x5c };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, sizeof(payload), &expected))
    TFAIL("mk text string");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tstr_u_umlaut_canonical(void) {
  /* "ü" = U+00FC, UTF-8 = C3 BC. */
  uint8_t bytes[] = { 0x62, 0xc3, 0xbc };
  static uint8_t payload[] = { 0xc3, 0xbc };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, sizeof(payload), &expected))
    TFAIL("mk text string");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tstr_water_canonical(void) {
  /* "水" = U+6C34, UTF-8 = E6 B0 B4. */
  uint8_t bytes[] = { 0x63, 0xe6, 0xb0, 0xb4 };
  static uint8_t payload[] = { 0xe6, 0xb0, 0xb4 };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, sizeof(payload), &expected))
    TFAIL("mk text string");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tstr_drachma_canonical(void) {
  /* "𐅑" = U+10151, UTF-8 = F0 90 85 91. */
  uint8_t bytes[] = { 0x64, 0xf0, 0x90, 0x85, 0x91 };
  static uint8_t payload[] = { 0xf0, 0x90, 0x85, 0x91 };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, sizeof(payload), &expected))
    TFAIL("mk text string");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* ---------- Extra array tests from gentest ---------- */

static int test_arr_nested_canonical(void) {
  /* [1, [2, 3], [4, 5]] */
  uint8_t bytes[] = {
    0x83,
    0x01,
    0x82, 0x02, 0x03,
    0x82, 0x04, 0x05
  };
  cbor_t inner1_items[2] = { cbor_v_mk_uint64(2), cbor_v_mk_uint64(3) };
  cbor_t inner2_items[2] = { cbor_v_mk_uint64(4), cbor_v_mk_uint64(5) };
  cbor_t inner1, inner2;
  if (!cbor_v_mk_array(inner1_items, 2, &inner1)) TFAIL("mk inner1");
  if (!cbor_v_mk_array(inner2_items, 2, &inner2)) TFAIL("mk inner2");
  cbor_t outer_items[3] = { cbor_v_mk_uint64(1), inner1, inner2 };
  cbor_t expected;
  if (!cbor_v_mk_array(outer_items, 3, &expected)) TFAIL("mk outer");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_arr_25_canonical(void) {
  /* [1, 2, ..., 25] — exercises the threshold at 24 items where the
     array length argument switches from 1-byte additional info to a
     1-byte argument. Encoded header is 0x98 0x19 (= 25). Items 1..23
     are 1-byte (0x01..0x17); items 24 and 25 each take 2 bytes
     (0x18 0x18, 0x18 0x19). Total: 2 + 23 + 2 + 2 = 29 bytes. */
  static uint8_t bytes[29];
  size_t off = 0;
  bytes[off++] = 0x98;
  bytes[off++] = 0x19;
  for (int i = 1; i <= 23; i++) bytes[off++] = (uint8_t)i;
  bytes[off++] = 0x18; bytes[off++] = 0x18;
  bytes[off++] = 0x18; bytes[off++] = 0x19;
  if (off != sizeof(bytes)) TFAIL("buffer size");

  cbor_t items[25];
  for (int i = 0; i < 25; i++) items[i] = cbor_v_mk_uint64(i + 1);
  cbor_t expected;
  if (!cbor_v_mk_array(items, 25, &expected)) TFAIL("mk array");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* ---------- Extra map/array tests from gentest ---------- */

/* {"a": 1, "b": [2, 3]} — heterogeneous canonical map. */
static int test_map_mixed_canonical(void) {
  uint8_t bytes[] = {
    0xa2,
    0x61, 'a', 0x01,
    0x61, 'b', 0x82, 0x02, 0x03
  };
  static uint8_t a[] = { 'a' };
  static uint8_t b[] = { 'b' };
  cbor_t k_a, k_b;
  if (!cbor_v_mk_text_string(a, 1, &k_a)) TFAIL("mk k_a");
  if (!cbor_v_mk_text_string(b, 1, &k_b)) TFAIL("mk k_b");
  cbor_t arr_items[2] = { cbor_v_mk_uint64(2), cbor_v_mk_uint64(3) };
  cbor_t arr;
  if (!cbor_v_mk_array(arr_items, 2, &arr)) TFAIL("mk arr");
  cbor_entry_t entries[2] = {
    cbor_v_mk_map_entry(k_a, cbor_v_mk_uint64(1)),
    cbor_v_mk_map_entry(k_b, arr)
  };
  cbor_t expected;
  if (!cbor_v_mk_map(entries, 2, &expected)) TFAIL("mk map");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* ["a", {"b": "c"}] */
static int test_arr_with_map_canonical(void) {
  uint8_t bytes[] = {
    0x82,
    0x61, 'a',
    0xa1, 0x61, 'b', 0x61, 'c'
  };
  static uint8_t a[] = { 'a' };
  static uint8_t b[] = { 'b' };
  static uint8_t c[] = { 'c' };
  cbor_t s_a, s_b, s_c;
  if (!cbor_v_mk_text_string(a, 1, &s_a)) TFAIL("mk s_a");
  if (!cbor_v_mk_text_string(b, 1, &s_b)) TFAIL("mk s_b");
  if (!cbor_v_mk_text_string(c, 1, &s_c)) TFAIL("mk s_c");
  cbor_entry_t inner_entries[1] = { cbor_v_mk_map_entry(s_b, s_c) };
  cbor_t inner_map;
  if (!cbor_v_mk_map(inner_entries, 1, &inner_map)) TFAIL("mk inner");
  cbor_t outer_items[2] = { s_a, inner_map };
  cbor_t expected;
  if (!cbor_v_mk_array(outer_items, 2, &expected)) TFAIL("mk outer");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* {"a":"A","b":"B","c":"C","d":"D","e":"E"} — 5-entry text-string map.
   Keys are already in canonical (lex) order. */
static int test_map_five_canonical(void) {
  uint8_t bytes[] = {
    0xa5,
    0x61, 'a', 0x61, 'A',
    0x61, 'b', 0x61, 'B',
    0x61, 'c', 0x61, 'C',
    0x61, 'd', 0x61, 'D',
    0x61, 'e', 0x61, 'E'
  };
  static uint8_t lower[5] = { 'a', 'b', 'c', 'd', 'e' };
  static uint8_t upper[5] = { 'A', 'B', 'C', 'D', 'E' };
  cbor_entry_t entries[5];
  for (int i = 0; i < 5; i++) {
    cbor_t k, v;
    if (!cbor_v_mk_text_string(&lower[i], 1, &k)) TFAIL("mk k");
    if (!cbor_v_mk_text_string(&upper[i], 1, &v)) TFAIL("mk v");
    entries[i] = cbor_v_mk_map_entry(k, v);
  }
  cbor_t expected;
  if (!cbor_v_mk_map(entries, 5, &expected)) TFAIL("mk map");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* ---------- UTF-8 tests (table-driven) ----------
 *
 * Ported from the 214 UTF-8 sub-tests of the original CBORDetTest.c /
 * CBORNondetTest.c suites. Each row says "construct a CBOR text string
 * from this byte sequence" and either expects construction to succeed
 * (then asserts a full validate / parse / equal round-trip), or
 * expects construction to be rejected because the bytes are not
 * well-formed UTF-8.
 *
 * Each row is wrapped into its own test function (so each gets its own
 * artefact file and benchmark line) by the X-macro UTF8_TESTS below.
 */

typedef struct {
  const uint8_t *bytes;
  size_t         len;
} utf8_input_t;

static int utf8_run_valid(const uint8_t *bytes, size_t len) {
  /* Construct a CBOR text string. */
  cbor_t expected;
  if (!cbor_v_mk_text_string((uint8_t *)bytes, len, &expected))
    TFAIL("text-string construction failed (expected success)");

  /* Build the canonical input bytes for this string. */
  uint8_t input[64];
  size_t off = 0;
  if (len <= 23) {
    input[off++] = (uint8_t)(0x60 | len);
  } else if (len <= 0xff) {
    input[off++] = 0x78;
    input[off++] = (uint8_t)len;
  } else {
    TFAIL("UTF-8 test payload too large");
  }
  if (off + len > sizeof(input)) TFAIL("input buffer overflow");
  memcpy(input + off, bytes, len);
  size_t total = off + len;
  return run_valid_match(input, total, expected);
}

static int utf8_run_invalid(const uint8_t *bytes, size_t len) {
  /* Construction must be rejected. We also persist the byte sequence to
     disk so cross-language consumers can verify their own validators. */
  cbor_t dummy;
  if (cbor_v_mk_text_string((uint8_t *)bytes, len, &dummy))
    TFAIL("text-string construction succeeded (expected failure)");
  if (maybe_write_input((uint8_t *)bytes, len)) return 1;
  return 0;
}

/* The X-macro: each entry is
     X(name_suffix, expected_validity, byte_literal...).
   `name_suffix` is appended to "utf8_" to form the test name.
   `expected_validity` is one of `valid` or `invalid`.
   The remaining variadic arguments are spliced into a uint8_t array
   initializer; this avoids commas-inside-braces being interpreted as
   extra macro arguments by the preprocessor.

   The byte sequences below are the union of the UTF-8 sub-tests
   originally living in CBORDetTest.c and CBORNondetTest.c, deduplicated
   and renamed to be unique. The numbering convention follows the
   original tests' "UTF-8 Test N.M" labels for traceability. */

#define UTF8_TESTS \
  X(t37_4, valid, 0x20, 0x00) \
  X(t37_3, invalid, 0x20, 0x00, 0x20, 0xff) \
  X(t37_2_1, valid, 0x20, 0x00, 0x35) \
  X(t37_2, invalid, 0xf0, 0x80, 0x80, 0x80) \
  X(t37_1, invalid, 0xe0, 0x80, 0x80) \
  X(t37_0, invalid, 0xc0, 0x80) \
  X(t35_0, invalid, 0xf4, 0x80, 0x80, 0x00) \
  X(t34_0, invalid, 0xf1, 0x80, 0x80, 0x00) \
  X(t33_0, invalid, 0xf0, 0x90, 0x80, 0x00) \
  X(t32_0, invalid, 0xed, 0x80, 0x00) \
  X(t31_0, invalid, 0xe0, 0x80, 0x00) \
  X(t30_4, invalid, 0xdf, 0x00) \
  X(t30_0, invalid, 0xc2, 0x00) \
  X(t5_0, valid, 0x00) \
  X(t36_9_1, valid, 0xef, 0xbf, 0xbe, 0x3d, 0xef, 0xbf, 0xbe, 0x2e) \
  X(t36_9, valid, 0xef, 0xbf, 0xbf, 0x3d, 0xef, 0xbf, 0xbf, 0x2e) \
  X(t36_10, invalid, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0x3d, 0xe0, 0x80, 0xaf, 0x2e) \
  X(t36_8, invalid, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0x3d, 0xed, 0xa0, 0x80, 0x2e) \
  X(t36_7, invalid, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0x3d, 0xf7, 0xbf, 0xbf, 0xbf, 0x2e) \
  X(t9_1, invalid, 0xc2, 0x41, 0x42) \
  X(t35_3, invalid, 0xf4, 0x80, 0x80, 0xff) \
  X(t35_2, invalid, 0xf4, 0x80, 0x80, 0xc0) \
  X(t35_1, invalid, 0xf4, 0x80, 0x80, 0x7f) \
  X(t34_3, invalid, 0xf1, 0x80, 0x80, 0xff) \
  X(t34_2, invalid, 0xf1, 0x80, 0x80, 0xc0) \
  X(t34_1, invalid, 0xf1, 0x80, 0x80, 0x7f) \
  X(t33_3, invalid, 0xf0, 0x90, 0x80, 0xff) \
  X(t33_2, invalid, 0xf0, 0x90, 0x80, 0xc0) \
  X(t33_1, invalid, 0xf0, 0x90, 0x80, 0x7f) \
  X(t32_3, invalid, 0xed, 0x80, 0xff) \
  X(t32_2, invalid, 0xed, 0x80, 0xc0) \
  X(t32_1, invalid, 0xed, 0x80, 0x7f) \
  X(t31_3, invalid, 0xe0, 0x80, 0xff) \
  X(t31_2, invalid, 0xe0, 0x80, 0xc0) \
  X(t31_1, invalid, 0xe0, 0x80, 0x7f) \
  X(t30_7, invalid, 0xdf, 0xff) \
  X(t30_6, invalid, 0xdf, 0xc0) \
  X(t30_5, invalid, 0xdf, 0x7f) \
  X(t30_3, invalid, 0xc2, 0xff) \
  X(t30_2, invalid, 0xc2, 0xc0) \
  X(t30_1, invalid, 0xc2, 0x7f) \
  X(t29_9, invalid, 0xff, 0x20) \
  X(t29_8, invalid, 0xf5, 0x20) \
  X(t29_7, invalid, 0xc1, 0x20) \
  X(t29_6, invalid, 0x81, 0x20) \
  X(t29_5, invalid, 0x20, 0x80, 0x20) \
  X(t29_4, invalid, 0x80, 0x20) \
  X(t29_3, invalid, 0x20, 0x21, 0x21, 0x23, 0x24, 0xfe) \
  X(t29_2, invalid, 0x20, 0x21, 0x21, 0x23, 0xfe, 0x20) \
  X(t29_1, invalid, 0x20, 0x80) \
  X(t29_0, invalid, 0x80) \
  X(t28_15, valid, 0xf4, 0x8f, 0xbf, 0xbf) \
  X(t28_14, valid, 0xf3, 0xbf, 0xbf, 0xbf) \
  X(t28_13, valid, 0xf3, 0xaf, 0xbf, 0xbf) \
  X(t28_12, valid, 0xf3, 0x9f, 0xbf, 0xbf) \
  X(t28_11, valid, 0xf3, 0x8f, 0xbf, 0xbf) \
  X(t28_10, valid, 0xf2, 0xbf, 0xbf, 0xbf) \
  X(t28_9, valid, 0xf2, 0xaf, 0xbf, 0xbf) \
  X(t28_8, valid, 0xf2, 0x9f, 0xbf, 0xbf) \
  X(t28_7, valid, 0xf2, 0x8f, 0xbf, 0xbf) \
  X(t28_6, valid, 0xf1, 0xbf, 0xbf, 0xbf) \
  X(t28_5, valid, 0xf1, 0xaf, 0xbf, 0xbf) \
  X(t28_4, valid, 0xf1, 0x9f, 0xbf, 0xbf) \
  X(t28_3, valid, 0xf1, 0x8f, 0xbf, 0xbf) \
  X(t28_2, valid, 0xf0, 0xbf, 0xbf, 0xbf) \
  X(t28_1, valid, 0xf0, 0xaf, 0xbf, 0xbf) \
  X(t28_0, valid, 0xf0, 0x9f, 0xbf, 0xbf) \
  X(t27_15, valid, 0xf4, 0x8f, 0xbf, 0xbe) \
  X(t27_14, valid, 0xf3, 0xbf, 0xbf, 0xbe) \
  X(t27_13, valid, 0xf3, 0xaf, 0xbf, 0xbe) \
  X(t27_12, valid, 0xf3, 0x9f, 0xbf, 0xbe) \
  X(t27_11, valid, 0xf3, 0x8f, 0xbf, 0xbe) \
  X(t27_10, valid, 0xf2, 0xbf, 0xbf, 0xbe) \
  X(t27_9, valid, 0xf2, 0xaf, 0xbf, 0xbe) \
  X(t27_8, valid, 0xf2, 0x9f, 0xbf, 0xbe) \
  X(t27_7, valid, 0xf2, 0x8f, 0xbf, 0xbe) \
  X(t27_6, valid, 0xf1, 0xbf, 0xbf, 0xbe) \
  X(t27_5, valid, 0xf1, 0xaf, 0xbf, 0xbe) \
  X(t27_4, valid, 0xf1, 0x9f, 0xbf, 0xbe) \
  X(t27_3, valid, 0xf1, 0x8f, 0xbf, 0xbe) \
  X(t27_2, valid, 0xf0, 0xbf, 0xbf, 0xbe) \
  X(t27_1, valid, 0xf0, 0xaf, 0xbf, 0xbe) \
  X(t27_0, valid, 0xf0, 0x9f, 0xbf, 0xbe) \
  X(t26_17, valid, 0xef, 0xb7, 0x9f) \
  X(t26_16, valid, 0xef, 0xb7, 0x9e) \
  X(t26_15, valid, 0xef, 0xb7, 0x9d) \
  X(t26_14, valid, 0xef, 0xb7, 0x9c) \
  X(t26_13, valid, 0xef, 0xb7, 0x9b) \
  X(t26_12, valid, 0xef, 0xb7, 0x9a) \
  X(t26_11, valid, 0xef, 0xb7, 0x99) \
  X(t26_10, valid, 0xef, 0xb7, 0x98) \
  X(t26_9, valid, 0xef, 0xb7, 0x97) \
  X(t26_8, valid, 0xef, 0xb7, 0x96) \
  X(t26_7, valid, 0xef, 0xb7, 0x95) \
  X(t26_6, valid, 0xef, 0xb7, 0x94) \
  X(t26_5, valid, 0xef, 0xb7, 0x93) \
  X(t26_4, valid, 0xef, 0xb7, 0x92) \
  X(t26_3, valid, 0xef, 0xb7, 0x91) \
  X(t26_2, valid, 0xef, 0xb7, 0x90) \
  X(t26_1, valid, 0xef, 0xbf, 0xbf) \
  X(t26_0, valid, 0xef, 0xbf, 0xbe) \
  X(t25_7, invalid, 0xed, 0xaf, 0xbf, 0xed, 0xbf, 0xbf) \
  X(t25_6, invalid, 0xed, 0xaf, 0xbf, 0xed, 0xb0, 0x80) \
  X(t25_5, invalid, 0xed, 0xae, 0x80, 0xed, 0xbf, 0xbf) \
  X(t25_4, invalid, 0xed, 0xae, 0x80, 0xed, 0xb0, 0x80) \
  X(t25_3, invalid, 0xed, 0xad, 0xbf, 0xed, 0xbf, 0xbf) \
  X(t25_2, invalid, 0xed, 0xad, 0xbf, 0xed, 0xb0, 0x80) \
  X(t25_1, invalid, 0xed, 0xa0, 0x80, 0xed, 0xbf, 0xbf) \
  X(t25_0, invalid, 0xed, 0xa0, 0x80, 0xed, 0xb0, 0x80) \
  X(t24_7, invalid, 0xed, 0xbf, 0xbf) \
  X(t24_6, invalid, 0xed, 0xbe, 0x80) \
  X(t24_5, invalid, 0xed, 0xb0, 0x80) \
  X(t24_4, invalid, 0xed, 0xaf, 0xbf) \
  X(t24_3, invalid, 0xed, 0xae, 0x80) \
  X(t24_2, invalid, 0xed, 0xad, 0xbf) \
  X(t24_0_2, invalid, 0x31, 0x32, 0x33, 0xed, 0xa0, 0x80, 0x31) \
  X(t24_0_1, invalid, 0xed, 0xa0, 0x80, 0x35) \
  X(t24_0, invalid, 0xed, 0xa0, 0x80) \
  X(t23_3, invalid, 0xf8, 0x87, 0xbf, 0xbf, 0xbf) \
  X(t23_2, invalid, 0xf0, 0x8f, 0xbf, 0xbf) \
  X(t23_1, invalid, 0xe0, 0x9f, 0xbf) \
  X(t23_0, invalid, 0xc1, 0xbf) \
  X(t22_6, invalid, 0xfc, 0x80, 0x80, 0x80, 0x80, 0xaf) \
  X(t22_5, invalid, 0xf8, 0x80, 0x80, 0x80, 0xaf) \
  X(t22_4, invalid, 0xf0, 0x80, 0x80, 0xaf) \
  X(t22_3, invalid, 0xe0, 0x80, 0xaf) \
  X(t22_2, invalid, 0xc0, 0xaf) \
  X(t21_6, invalid, 0x37, 0x38, 0x39, 0xfe) \
  X(t21_5, invalid, 0x37, 0x38, 0xfe) \
  X(t21_4, invalid, 0x37, 0xff) \
  X(t21_3, invalid, 0xff) \
  X(t21_2, invalid, 0xfe) \
  X(t21_1, invalid, 0x81) \
  X(t19_6, invalid, 0x31, 0x32, 0x33, 0xef, 0x80, 0xf0) \
  X(t19_5, invalid, 0x31, 0x32, 0x33, 0xef, 0x80) \
  X(t19_4, invalid, 0xfd, 0xbf, 0xbf, 0xbf, 0xbf) \
  X(t19_3, invalid, 0xfb, 0xbf, 0xbf, 0xbf) \
  X(t19_2, invalid, 0xf7, 0xbf, 0xbf) \
  X(t19_1, invalid, 0xef, 0xbf) \
  X(t19_0, invalid, 0xdf) \
  X(t18_4, invalid, 0xfc, 0x80, 0x80, 0x80, 0x80) \
  X(t18_3, invalid, 0xf8, 0x80, 0x80, 0x80) \
  X(t18_2, invalid, 0xf0, 0x80, 0x80) \
  X(t18_1, invalid, 0xe0, 0x80) \
  X(t18_0, invalid, 0xc0) \
  X(t17_1, invalid, 0xfd, 0x20) \
  X(t17_0, invalid, 0xfc, 0x20) \
  X(t16_3, invalid, 0xfb, 0x20) \
  X(t16_2, invalid, 0xfa, 0x20) \
  X(t16_1, invalid, 0xf9, 0x20) \
  X(t16_0, invalid, 0xf8, 0x20) \
  X(t15_3, invalid, 0xf6, 0x20, 0xf7, 0x20) \
  X(t15_2, invalid, 0xf4, 0x20, 0xf5, 0x20) \
  X(t15_1, invalid, 0xf2, 0x20, 0xf3, 0x20) \
  X(t15_0, invalid, 0xf0, 0x20, 0xf1, 0x20) \
  X(t14_5_1, invalid, 0xe1, 0x80, 0xe2, 0xf0, 0x91, 0x92, 0xf1, 0xbf, 0x41) \
  X(t14_4_2, invalid, 0xf4, 0x91, 0x92, 0x93, 0xff, 0x41, 0x80, 0xbf, 0x42) \
  X(t14_4_1, invalid, 0xed, 0xa0, 0x80, 0xed, 0xbf, 0xbf, 0xed, 0xaf, 0x41) \
  X(t14_4_0, invalid, 0xc0, 0xaf, 0xe0, 0x80, 0xbf, 0xf0, 0x81, 0x82, 0x41) \
  X(t14_3, invalid, 0xec, 0x20, 0xed, 0x20, 0xee, 0x20, 0xef, 0x20) \
  X(t14_2, invalid, 0xe8, 0x20, 0xe9, 0x20, 0xea, 0x20, 0xeb, 0x20) \
  X(t14_1, invalid, 0xe4, 0x20, 0xe5, 0x20, 0xe6, 0x20, 0xe7, 0x20) \
  X(t14_0, invalid, 0xe0, 0x20, 0xe1, 0x20, 0xe2, 0x20, 0xe3, 0x20) \
  X(t13_7, invalid, 0xdc, 0x20, 0xdd, 0x20, 0xde, 0x20, 0xdf, 0x20) \
  X(t13_6, invalid, 0xd8, 0x20, 0xd9, 0x20, 0xda, 0x20, 0xdb, 0x20) \
  X(t13_5, invalid, 0xd4, 0x20, 0xd5, 0x20, 0xd6, 0x20, 0xd7, 0x20) \
  X(t13_4, invalid, 0xd0, 0x20, 0xd1, 0x20, 0xd2, 0x20, 0xd3, 0x20) \
  X(t13_3, invalid, 0xcc, 0x20, 0xcd, 0x20, 0xce, 0x20, 0xcf, 0x20) \
  X(t13_2, invalid, 0xc8, 0x20, 0xc9, 0x20, 0xca, 0x20, 0xcb, 0x20) \
  X(t13_1, invalid, 0xc4, 0x20, 0xc5, 0x20, 0xc6, 0x20, 0xc7, 0x20) \
  X(t13_0, invalid, 0xc0, 0x20, 0xc1, 0x20, 0xc2, 0x20, 0xc3, 0x20) \
  X(t12_7, invalid, 0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf) \
  X(t12_6, invalid, 0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7) \
  X(t12_5, invalid, 0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf) \
  X(t12_4, invalid, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7) \
  X(t12_3, invalid, 0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f) \
  X(t12_2, invalid, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97) \
  X(t12_1, invalid, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f) \
  X(t12_0, invalid, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87) \
  X(t11_6, invalid, 0x80, 0xbf, 0x80, 0xbf, 0x80, 0xbf) \
  X(t11_5, invalid, 0x80, 0xbf, 0x80, 0xbf, 0x80) \
  X(t11_4, invalid, 0x80, 0xbf, 0x80, 0xbf) \
  X(t11_3, invalid, 0x80, 0xbf, 0x80) \
  X(t11_2, invalid, 0x80, 0xbf) \
  X(t11_1, invalid, 0xbf) \
  X(t6_5, invalid, 0xf7, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf) \
  X(t6_4, invalid, 0xf7, 0xbf, 0xbf, 0xbf, 0xbf, 0xbf) \
  X(t6_3, invalid, 0xfc, 0x84, 0x80, 0x80, 0x80, 0x80) \
  X(t6_2, invalid, 0xf7, 0xbf, 0xbf, 0xbf, 0xbf) \
  X(t6_1, invalid, 0xf8, 0x88, 0x80, 0x80, 0x80) \
  X(t6_0_1, invalid, 0xf4, 0x90, 0x80, 0x80) \
  X(t6_0, invalid, 0xf7, 0xbf, 0xbf, 0xbf) \
  X(t22_7, valid, 0xe0, 0xa0, 0x80) \
  X(t22_1, valid, 0x2f) \
  X(t10_2, valid, 0xef, 0xbf, 0xbd) \
  X(t10_1, valid, 0xee, 0x80, 0x80) \
  X(t8_1, valid, 0xdf, 0xbf) \
  X(t8_0, valid, 0x7f) \
  X(t7_3, valid, 0xc2, 0x82) \
  X(t7_2, valid, 0xc2, 0x81) \
  X(t7_1, valid, 0xc2, 0x80) \
  X(t5_3, valid, 0xf0, 0x90, 0x80, 0x80) \
  X(t4_0, valid, 0xf0, 0x9d, 0x92, 0x9c) \
  X(t3_0, valid, 0xe2, 0x80, 0x90) \
  X(t2_1_0, valid, 0xc2, 0xa9) \
  X(t1_0_1, valid, 0x31)

/* Materialise one test function per row. */
#define X(suffix, validity, ...)                                              \
  static int test_utf8_##suffix(void) {                                       \
    static const uint8_t b[] = { __VA_ARGS__ };                               \
    return utf8_run_##validity(b, sizeof(b));                                 \
  }
UTF8_TESTS
#undef X

/* ---------- Large-array recursion-budget tests (from main.c) ----------
 *
 * Build a CBOR array of depth LARGE_ARR_DEPTH whose only leaf is the
 * uint 1, encoded as bytes 0x81 0x81 ... 0x81 0x01. The original
 * `large_array_test()` validates the well-formed buffer (must succeed)
 * and a truncated copy missing the leaf (must fail).
 */
#define LARGE_ARR_DEPTH 2200

static int test_arr_2200_deep_canonical(void) {
  static uint8_t bytes[LARGE_ARR_DEPTH + 1];
  static int initialized = 0;
  if (!initialized) {
    for (int i = 0; i < LARGE_ARR_DEPTH; i++) bytes[i] = 0x81;
    bytes[LARGE_ARR_DEPTH] = 0x01;
    initialized = 1;
  }
  /* Build the matching CBOR object through the API: leaf 1, then wrap
     LARGE_ARR_DEPTH times in singleton arrays. We can't put 2201
     cbor_t values on the stack, so use a heap allocation for this one
     test. */
  cbor_t *levels = (cbor_t *)malloc(sizeof(cbor_t) * (LARGE_ARR_DEPTH + 1));
  if (!levels) TFAIL("malloc");
  levels[0] = cbor_v_mk_uint64(1);
  for (int i = 1; i <= LARGE_ARR_DEPTH; i++) {
    if (!cbor_v_mk_array(&levels[i - 1], 1, &levels[i])) {
      free(levels);
      TFAIL("mk array level");
    }
  }
  cbor_t expected = levels[LARGE_ARR_DEPTH];
  int rc = run_valid_match(bytes, sizeof(bytes), expected);
  free(levels);
  return rc;
}

static int test_arr_2200_deep_truncated_invalid(void) {
  /* Same byte buffer as above but missing the 0x01 leaf — pure stream
     of LARGE_ARR_DEPTH 0x81 bytes describing a never-terminated tower
     of singleton arrays. */
  static uint8_t bytes[LARGE_ARR_DEPTH];
  static int initialized = 0;
  if (!initialized) {
    for (int i = 0; i < LARGE_ARR_DEPTH; i++) bytes[i] = 0x81;
    initialized = 1;
  }
  return run_invalid(bytes, sizeof(bytes));
}

/* ---------- qcbortests ports ----------
 *
 * Ported from src/cbor/pulse/nondet/c/test/qcbortests.c. These tests
 * originate from Laurence Lundblade's QCBOR test suite.
 */

/* IntegerValuesParseTestInternal: a 47-element array of integers
 * spanning the int64/uint64 boundaries, including INT64_MIN, all
 * powers of 2^k - 1 / 2^k / 2^k + 1 around k=8/16/32/63, and the
 * top of UINT64. The reference encoding is canonical. */
static int test_arr_int_boundaries_canonical(void) {
  static const int64_t IntegerValues[] = {
    -9223372036854775807LL - 1,
    -4294967297LL, -4294967296LL, -4294967295LL, -4294967294LL,
    -2147483648LL, -2147483647LL,
    -65538, -65537, -65536, -65535, -65534,
    -257, -256, -255, -254,
    -25, -24, -23, -1,
    0, 0, 1, 22, 23, 24, 25, 26,
    254, 255, 256, 257,
    65534, 65535, 65536, 65537, 65538,
    2147483647, 2147483647, 2147483648LL, 2147483649LL,
    4294967294LL, 4294967295LL, 4294967296LL, 4294967297LL,
    9223372036854775807LL
  };
  static const uint8_t bytes[] = {
    0x98, 0x2f, 0x3b, 0x7f, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0x3b, 0x00, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x3a, 0xff, 0xff, 0xff,
    0xff, 0x3a, 0xff, 0xff, 0xff, 0xfe, 0x3a, 0xff,
    0xff, 0xff, 0xfd, 0x3a, 0x7f, 0xff, 0xff, 0xff,
    0x3a, 0x7f, 0xff, 0xff, 0xfe, 0x3a, 0x00, 0x01,
    0x00, 0x01, 0x3a, 0x00, 0x01, 0x00, 0x00, 0x39,
    0xff, 0xff, 0x39, 0xff, 0xfe, 0x39, 0xff, 0xfd,
    0x39, 0x01, 0x00, 0x38, 0xff, 0x38, 0xfe, 0x38,
    0xfd, 0x38, 0x18, 0x37, 0x36, 0x20, 0x00, 0x00,
    0x01, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19, 0x18,
    0x1a, 0x18, 0xfe, 0x18, 0xff, 0x19, 0x01, 0x00,
    0x19, 0x01, 0x01, 0x19, 0xff, 0xfe, 0x19, 0xff,
    0xff, 0x1a, 0x00, 0x01, 0x00, 0x00, 0x1a, 0x00,
    0x01, 0x00, 0x01, 0x1a, 0x00, 0x01, 0x00, 0x02,
    0x1a, 0x7f, 0xff, 0xff, 0xff, 0x1a, 0x7f, 0xff,
    0xff, 0xff, 0x1a, 0x80, 0x00, 0x00, 0x00, 0x1a,
    0x80, 0x00, 0x00, 0x01, 0x1a, 0xff, 0xff, 0xff,
    0xfe, 0x1a, 0xff, 0xff, 0xff, 0xff, 0x1b, 0x00,
    0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x1b,
    0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
    0x1b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff
  };
  enum { N = sizeof(IntegerValues) / sizeof(IntegerValues[0]) };
  cbor_t items[N + 1];
  for (size_t i = 0; i < N; i++) {
    int64_t v = IntegerValues[i];
    items[i] = (v < 0) ? cbor_v_mk_neg_int64((uint64_t)(-1 - v))
                       : cbor_v_mk_uint64((uint64_t)v);
  }
  /* Tail entry: 2^64 - 1, the maximum unsigned 64-bit value. */
  items[N] = cbor_v_mk_uint64(0xffffffffffffffffULL);
  cbor_t expected;
  if (!cbor_v_mk_array(items, N + 1, &expected)) TFAIL("mk array");
  return run_valid_match((uint8_t *)bytes, sizeof(bytes), expected);
}

/* CheckEmpties: [0, [], [[], [0], {}, {1: {}, 2: {}, 3: []}]] */
static int test_arr_empties_canonical(void) {
  static uint8_t bytes[] = {
    0x83, 0x00, 0x80, 0x84, 0x80, 0x81, 0x00, 0xa0,
    0xa3, 0x01, 0xa0, 0x02, 0xa0, 0x03, 0x80
  };
  cbor_t z[3];
  z[0] = cbor_v_mk_uint64(0);

  cbor_t empty_arr_buf[1] = { cbor_v_mk_uint64(0) }; /* unused */
  if (!cbor_v_mk_array(empty_arr_buf, 0, &z[1])) TFAIL("mk z[1]");

  cbor_t y[4];
  if (!cbor_v_mk_array(empty_arr_buf, 0, &y[0])) TFAIL("mk y[0]");
  cbor_t leaf_arr[1] = { cbor_v_mk_uint64(0) };
  if (!cbor_v_mk_array(leaf_arr, 1, &y[1])) TFAIL("mk y[1]");
  cbor_entry_t empty_map_buf[1] = {
    cbor_v_mk_map_entry(cbor_v_mk_uint64(0), cbor_v_mk_uint64(0))
  };
  if (!cbor_v_mk_map(empty_map_buf, 0, &y[2])) TFAIL("mk y[2]");

  cbor_entry_t inner[3];
  cbor_t inner_v0, inner_v1, inner_v2;
  if (!cbor_v_mk_map(empty_map_buf, 0, &inner_v0)) TFAIL("mk inner_v0");
  if (!cbor_v_mk_map(empty_map_buf, 0, &inner_v1)) TFAIL("mk inner_v1");
  if (!cbor_v_mk_array(empty_arr_buf, 0, &inner_v2)) TFAIL("mk inner_v2");
  inner[0] = cbor_v_mk_map_entry(cbor_v_mk_uint64(1), inner_v0);
  inner[1] = cbor_v_mk_map_entry(cbor_v_mk_uint64(2), inner_v1);
  inner[2] = cbor_v_mk_map_entry(cbor_v_mk_uint64(3), inner_v2);
  if (!cbor_v_mk_map(inner, 3, &y[3])) TFAIL("mk y[3]");

  if (!cbor_v_mk_array(y, 4, &z[2])) TFAIL("mk z[2]");

  cbor_t expected;
  if (!cbor_v_mk_array(z, 3, &expected)) TFAIL("mk outer");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* ValidMapEncoded: a complex 3-entry top-level map containing strings,
 * an array of strings, and an inner 4-entry map. The text-string keys
 * are NOT in canonical (length-then-lex) order in the reference
 * encoding, so this is a non-deterministic-encoding-only test:
 * det must reject it; nondet must accept it.
 */
static int test_map_qcbor_complex_nondet(void) {
  static uint8_t bytes[] = {
    0xa3, 0x6d, 0x66, 0x69, 0x72, 0x73, 0x74, 0x20,
    0x69, 0x6e, 0x74, 0x65, 0x67, 0x65, 0x72, 0x18,
    0x2a, 0x77, 0x61, 0x6e, 0x20, 0x61, 0x72, 0x72,
    0x61, 0x79, 0x20, 0x6f, 0x66, 0x20, 0x74, 0x77,
    0x6f, 0x20, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67,
    0x73, 0x82, 0x67, 0x73, 0x74, 0x72, 0x69, 0x6e,
    0x67, 0x31, 0x67, 0x73, 0x74, 0x72, 0x69, 0x6e,
    0x67, 0x32, 0x6c, 0x6d, 0x61, 0x70, 0x20, 0x69,
    0x6e, 0x20, 0x61, 0x20, 0x6d, 0x61, 0x70, 0xa4,
    0x67, 0x62, 0x79, 0x74, 0x65, 0x73, 0x20, 0x31,
    0x44, 0x78, 0x78, 0x78, 0x78, 0x67, 0x62, 0x79,
    0x74, 0x65, 0x73, 0x20, 0x32, 0x44, 0x79, 0x79,
    0x79, 0x79, 0x6b, 0x61, 0x6e, 0x6f, 0x74, 0x68,
    0x65, 0x72, 0x20, 0x69, 0x6e, 0x74, 0x18, 0x62,
    0x66, 0x74, 0x65, 0x78, 0x74, 0x20, 0x32, 0x78,
    0x1e, 0x6c, 0x69, 0x65, 0x73, 0x2c, 0x20, 0x64,
    0x61, 0x6d, 0x6e, 0x20, 0x6c, 0x69, 0x65, 0x73,
    0x20, 0x61, 0x6e, 0x64, 0x20, 0x73, 0x74, 0x61,
    0x74, 0x69, 0x73, 0x74, 0x69, 0x63, 0x73
  };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  /* Helper: text-string from a string literal. */
  #define TS(name, str) \
    static uint8_t name##_b[] = str; \
    cbor_t name; \
    if (!cbor_v_mk_text_string(name##_b, sizeof(name##_b) - 1, &name)) \
      TFAIL("mk " #name)

  TS(k_first, "first integer");
  TS(k_arr,   "an array of two strings");
  TS(k_inner, "map in a map");
  TS(s1, "string1");
  TS(s2, "string2");
  TS(k_b1, "bytes 1");
  TS(k_b2, "bytes 2");
  TS(k_anint, "another int");
  TS(k_text2, "text 2");
  TS(v_text2, "lies, damn lies and statistics");
  #undef TS

  static uint8_t bytes1[] = { 0x78, 0x78, 0x78, 0x78 };
  static uint8_t bytes2[] = { 0x79, 0x79, 0x79, 0x79 };
  cbor_t v_b1, v_b2;
  if (!cbor_v_mk_byte_string(bytes1, sizeof(bytes1), &v_b1)) TFAIL("mk b1");
  if (!cbor_v_mk_byte_string(bytes2, sizeof(bytes2), &v_b2)) TFAIL("mk b2");

  cbor_entry_t inner_entries[4] = {
    cbor_v_mk_map_entry(k_b1, v_b1),
    cbor_v_mk_map_entry(k_b2, v_b2),
    cbor_v_mk_map_entry(k_anint, cbor_v_mk_uint64(98)),
    cbor_v_mk_map_entry(k_text2, v_text2)
  };
  cbor_t inner_map;
  if (!cbor_v_mk_map(inner_entries, 4, &inner_map)) TFAIL("mk inner map");

  cbor_t arr_items[2] = { s1, s2 };
  cbor_t arr;
  if (!cbor_v_mk_array(arr_items, 2, &arr)) TFAIL("mk arr");

  cbor_entry_t outer_entries[3] = {
    cbor_v_mk_map_entry(k_first, cbor_v_mk_uint64(42)),
    cbor_v_mk_map_entry(k_arr,   arr),
    cbor_v_mk_map_entry(k_inner, inner_map)
  };
  cbor_t expected;
  if (!cbor_v_mk_map(outer_entries, 3, &expected)) TFAIL("mk outer map");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* ---------- General invalid encodings ---------- */

static int test_invalid_truncated(void) {
  /* Header 0x18 says a 1-byte argument follows, but no byte present. */
  uint8_t bytes[] = { 0x18 };
  return run_invalid(bytes, sizeof(bytes));
}

static int test_invalid_bstr_short(void) {
  /* Byte string of length 4 but only 2 bytes follow. */
  uint8_t bytes[] = { 0x44, 0x01, 0x02 };
  return run_invalid(bytes, sizeof(bytes));
}

static int test_invalid_arr_short(void) {
  /* Array of length 3 but only 2 items present. */
  uint8_t bytes[] = { 0x83, 0x01, 0x02 };
  return run_invalid(bytes, sizeof(bytes));
}

static int test_invalid_map_short(void) {
  /* Map of length 2 but only 1 entry follows. */
  uint8_t bytes[] = { 0xa2, 0x01, 0x02 };
  return run_invalid(bytes, sizeof(bytes));
}

/* Indefinite-length arrays (0x9f) are explicitly unsupported per spec. */
static int test_invalid_indefinite(void) {
  /* Indefinite-length array of one item terminated by break. */
  uint8_t bytes[] = { 0x9f, 0x01, 0xff };
  return run_invalid(bytes, sizeof(bytes));
}

/* ============================================================
 *   Additional tests added to maximize branch coverage of
 *   src/cbor/pulse/{det,nondet}/c/CBOR{Det,Nondet}.c
 *
 *   Each test below targets a distinct edge case or branch that
 *   was not previously exercised by the existing suite. See the
 *   per-test comments for the specific branch targeted.
 * ============================================================ */

/* ---- Helper: trailing-byte run.
 *   Validate must succeed but consume strictly fewer than `len` bytes
 *   (i.e. detect that the buffer has well-formed CBOR followed by garbage).
 *   Then the prefix must parse to `expected`.
 */
static int run_valid_trailing(uint8_t *bytes, size_t len, size_t expected_prefix,
                              cbor_t expected) {
  if (maybe_write_input(bytes, len)) return 1;
  size_t vsize = cbor_v_validate(bytes, len);
  if (vsize == 0) TFAIL("validation rejected the prefix");
  if (vsize != expected_prefix)
    TFAIL("validation consumed %zu bytes, expected prefix %zu",
          vsize, expected_prefix);
  if (vsize >= len)
    TFAIL("validation consumed %zu of %zu (no trailing detected)",
          vsize, len);
  cbor_t parsed = cbor_v_parse(bytes, vsize);
  if (!cbor_v_equal(parsed, expected))
    TFAIL("trailing-byte parse not equal to expected");
  return 0;
}

/* ---------- Major type 0: integer boundaries (canonical) ---------- */

static int test_uint_uint8_max_canonical(void) {
  /* 0xff = 255: largest value in 1-byte argument form. */
  uint8_t bytes[] = { 0x18, 0xff };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_uint64(0xff));
}

static int test_uint_256_canonical(void) {
  /* 256: smallest value requiring 2-byte argument form. */
  uint8_t bytes[] = { 0x19, 0x01, 0x00 };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_uint64(256));
}

static int test_uint_uint16_max_canonical(void) {
  /* 0xffff = 65535: largest value in 2-byte argument form. */
  uint8_t bytes[] = { 0x19, 0xff, 0xff };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_uint64(0xffff));
}

static int test_uint_65536_canonical(void) {
  /* 65536: smallest value requiring 4-byte argument form. */
  uint8_t bytes[] = { 0x1a, 0x00, 0x01, 0x00, 0x00 };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_uint64(65536));
}

static int test_uint_uint32_max_canonical(void) {
  /* 0xffffffff: largest value in 4-byte argument form. */
  uint8_t bytes[] = { 0x1a, 0xff, 0xff, 0xff, 0xff };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_uint64(0xffffffffULL));
}

static int test_uint_uint64_max_minus_one_canonical(void) {
  /* 2^64 - 2 — exercises 8-byte path one below max. */
  uint8_t bytes[] = { 0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_uint64(0xfffffffffffffffeULL));
}

static int test_uint_uint64_max_canonical(void) {
  /* 2^64 - 1: maximum unsigned 64-bit value. */
  uint8_t bytes[] = { 0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_uint64(0xffffffffffffffffULL));
}

/* ---------- Major type 0: non-canonical encodings ---------- */

static int test_uint_24_two_byte_nondet(void) {
  /* Value 24 forced into 2-byte form. Det rejects (canonical = 0x18 0x18). */
  uint8_t bytes[] = { 0x19, 0x00, 0x18 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  return run_valid_no_match(bytes, sizeof(bytes), cbor_v_mk_uint64(24));
#endif
}

static int test_uint_24_four_byte_nondet(void) {
  uint8_t bytes[] = { 0x1a, 0x00, 0x00, 0x00, 0x18 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  return run_valid_no_match(bytes, sizeof(bytes), cbor_v_mk_uint64(24));
#endif
}

static int test_uint_24_eight_byte_nondet(void) {
  uint8_t bytes[] = { 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  return run_valid_no_match(bytes, sizeof(bytes), cbor_v_mk_uint64(24));
#endif
}

static int test_uint_uint8_max_two_byte_nondet(void) {
  /* 0xff in 2-byte form: leading-zero argument that fits in 1 byte. */
  uint8_t bytes[] = { 0x19, 0x00, 0xff };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  return run_valid_no_match(bytes, sizeof(bytes), cbor_v_mk_uint64(0xff));
#endif
}

static int test_uint_uint16_max_four_byte_nondet(void) {
  /* 0xffff in 4-byte form. */
  uint8_t bytes[] = { 0x1a, 0x00, 0x00, 0xff, 0xff };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  return run_valid_no_match(bytes, sizeof(bytes), cbor_v_mk_uint64(0xffff));
#endif
}

/* ---------- Major type 1: negative integer boundaries ---------- */

static int test_neg_minus_256_canonical(void) {
  /* -256 = -1 - 0xff: last value in 1-byte arg form. */
  uint8_t bytes[] = { 0x38, 0xff };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_neg_int64(0xff));
}

static int test_neg_minus_257_canonical(void) {
  /* -257 = -1 - 0x100: first value requiring 2-byte arg. */
  uint8_t bytes[] = { 0x39, 0x01, 0x00 };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_neg_int64(0x100));
}

static int test_neg_minus_65536_canonical(void) {
  /* -65536: last in 2-byte arg form. */
  uint8_t bytes[] = { 0x39, 0xff, 0xff };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_neg_int64(0xffff));
}

static int test_neg_minus_65537_canonical(void) {
  /* -65537: first in 4-byte arg form. */
  uint8_t bytes[] = { 0x3a, 0x00, 0x01, 0x00, 0x00 };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_neg_int64(0x10000));
}

static int test_neg_minus_2pow32_canonical(void) {
  /* -2^32 = -1 - 0xffffffff: last in 4-byte arg form. */
  uint8_t bytes[] = { 0x3a, 0xff, 0xff, 0xff, 0xff };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_neg_int64(0xffffffffULL));
}

static int test_neg_minus_2pow32_minus_one_canonical(void) {
  /* -2^32 - 1: first in 8-byte arg form. */
  uint8_t bytes[] = { 0x3b, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00 };
  return run_valid_match(bytes, sizeof(bytes), cbor_v_mk_neg_int64(0x100000000ULL));
}

static int test_neg_min_canonical(void) {
  /* -2^64 = -1 - (2^64 - 1): the smallest representable value. */
  uint8_t bytes[] = { 0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };
  return run_valid_match(bytes, sizeof(bytes),
                         cbor_v_mk_neg_int64(0xffffffffffffffffULL));
}

static int test_neg_minus_one_two_byte_nondet(void) {
  /* -1 in 2-byte form. */
  uint8_t bytes[] = { 0x39, 0x00, 0x00 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  return run_valid_no_match(bytes, sizeof(bytes), cbor_v_mk_neg_int64(0));
#endif
}

/* ---------- Major type 2: byte-string length boundaries ---------- */

/* Small static buffers used for the length-boundary tests below. */
static uint8_t g_buf256[256];
static uint8_t g_input_buf[512];
static int g_buf256_initialized = 0;

static void init_buf256(void) {
  if (!g_buf256_initialized) {
    for (int i = 0; i < 256; i++) g_buf256[i] = (uint8_t)i;
    g_buf256_initialized = 1;
  }
}

static int test_bstr_23_canonical(void) {
  /* Length 23: last in short additional-info form (header 0x57). */
  init_buf256();
  g_input_buf[0] = 0x57;
  memcpy(g_input_buf + 1, g_buf256, 23);
  cbor_t expected;
  if (!cbor_v_mk_byte_string(g_buf256, 23, &expected)) TFAIL("mk bstr 23");
  return run_valid_match(g_input_buf, 24, expected);
}

static int test_bstr_24_canonical(void) {
  /* Length 24: first requiring 1-byte argument (header 0x58 0x18). */
  init_buf256();
  g_input_buf[0] = 0x58;
  g_input_buf[1] = 0x18;
  memcpy(g_input_buf + 2, g_buf256, 24);
  cbor_t expected;
  if (!cbor_v_mk_byte_string(g_buf256, 24, &expected)) TFAIL("mk bstr 24");
  return run_valid_match(g_input_buf, 26, expected);
}

static int test_bstr_255_canonical(void) {
  /* Length 255: last in 1-byte arg form (header 0x58 0xff). */
  init_buf256();
  g_input_buf[0] = 0x58;
  g_input_buf[1] = 0xff;
  memcpy(g_input_buf + 2, g_buf256, 255);
  cbor_t expected;
  if (!cbor_v_mk_byte_string(g_buf256, 255, &expected)) TFAIL("mk bstr 255");
  return run_valid_match(g_input_buf, 257, expected);
}

static int test_bstr_256_canonical(void) {
  /* Length 256: first requiring 2-byte arg form (header 0x59 0x01 0x00). */
  init_buf256();
  g_input_buf[0] = 0x59;
  g_input_buf[1] = 0x01;
  g_input_buf[2] = 0x00;
  memcpy(g_input_buf + 3, g_buf256, 256);
  cbor_t expected;
  if (!cbor_v_mk_byte_string(g_buf256, 256, &expected)) TFAIL("mk bstr 256");
  return run_valid_match(g_input_buf, 259, expected);
}

static int test_bstr_short_two_byte_nondet(void) {
  /* 4-byte bstr with length encoded in 2 bytes. Det rejects. */
  uint8_t bytes[] = { 0x59, 0x00, 0x04, 0xde, 0xad, 0xbe, 0xef };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  static uint8_t payload[] = { 0xde, 0xad, 0xbe, 0xef };
  cbor_t expected;
  if (!cbor_v_mk_byte_string(payload, 4, &expected)) TFAIL("mk bstr");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

static int test_bstr_short_eight_byte_nondet(void) {
  /* 4-byte bstr with length encoded in 8 bytes. */
  uint8_t bytes[] = { 0x5b, 0,0,0,0,0,0,0,4, 0xde, 0xad, 0xbe, 0xef };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  static uint8_t payload[] = { 0xde, 0xad, 0xbe, 0xef };
  cbor_t expected;
  if (!cbor_v_mk_byte_string(payload, 4, &expected)) TFAIL("mk bstr");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

static int test_bstr_oversized_invalid(void) {
  /* Header claims 0xffff bytes follow but only 2 do. Validate must reject. */
  uint8_t bytes[] = { 0x59, 0xff, 0xff, 0x00, 0x01 };
  return run_invalid(bytes, sizeof(bytes));
}

/* ---------- Major type 3: text-string length boundaries ----------
 * Use 'a' (0x61) bytes throughout so the contents are valid UTF-8. */

static uint8_t g_atext[256];
static int     g_atext_init = 0;
static void init_atext(void) {
  if (!g_atext_init) { memset(g_atext, 'a', sizeof(g_atext)); g_atext_init = 1; }
}

static int test_tstr_23_canonical(void) {
  init_atext();
  g_input_buf[0] = 0x77;
  memcpy(g_input_buf + 1, g_atext, 23);
  cbor_t expected;
  if (!cbor_v_mk_text_string(g_atext, 23, &expected)) TFAIL("mk tstr 23");
  return run_valid_match(g_input_buf, 24, expected);
}

static int test_tstr_24_canonical(void) {
  init_atext();
  g_input_buf[0] = 0x78;
  g_input_buf[1] = 0x18;
  memcpy(g_input_buf + 2, g_atext, 24);
  cbor_t expected;
  if (!cbor_v_mk_text_string(g_atext, 24, &expected)) TFAIL("mk tstr 24");
  return run_valid_match(g_input_buf, 26, expected);
}

static int test_tstr_255_canonical(void) {
  init_atext();
  g_input_buf[0] = 0x78;
  g_input_buf[1] = 0xff;
  memcpy(g_input_buf + 2, g_atext, 255);
  cbor_t expected;
  if (!cbor_v_mk_text_string(g_atext, 255, &expected)) TFAIL("mk tstr 255");
  return run_valid_match(g_input_buf, 257, expected);
}

static int test_tstr_256_canonical(void) {
  init_atext();
  g_input_buf[0] = 0x79;
  g_input_buf[1] = 0x01;
  g_input_buf[2] = 0x00;
  memcpy(g_input_buf + 3, g_atext, 256);
  cbor_t expected;
  if (!cbor_v_mk_text_string(g_atext, 256, &expected)) TFAIL("mk tstr 256");
  return run_valid_match(g_input_buf, 259, expected);
}

static int test_tstr_a_eight_byte_nondet(void) {
  /* 1-char tstr in 8-byte length form. */
  uint8_t bytes[] = { 0x7b, 0,0,0,0,0,0,0,1, 'a' };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  static uint8_t payload[] = { 'a' };
  cbor_t expected;
  if (!cbor_v_mk_text_string(payload, 1, &expected)) TFAIL("mk tstr");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

static int test_tstr_oversized_invalid(void) {
  /* Header claims 0xffff bytes but only 2 follow. */
  uint8_t bytes[] = { 0x79, 0xff, 0xff, 'a', 'b' };
  return run_invalid(bytes, sizeof(bytes));
}

/* ---------- Major type 4: array length boundaries ---------- */

static int test_arr_23_canonical(void) {
  /* Length 23: last in short additional-info form (header 0x97). */
  uint8_t bytes[24];
  bytes[0] = 0x97;
  for (int i = 0; i < 23; i++) bytes[i + 1] = (uint8_t)i; /* values 0..22 */
  cbor_t items[23];
  for (int i = 0; i < 23; i++) items[i] = cbor_v_mk_uint64((uint64_t)i);
  cbor_t expected;
  if (!cbor_v_mk_array(items, 23, &expected)) TFAIL("mk arr");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_arr_24_canonical(void) {
  /* Length 24: first requiring 1-byte arg form (header 0x98 0x18). */
  uint8_t bytes[26];
  bytes[0] = 0x98;
  bytes[1] = 0x18;
  for (int i = 0; i < 23; i++) bytes[i + 2] = (uint8_t)i;
  /* Item 23 is value 23 = 0x17 (still 1 byte). */
  bytes[25] = 0x17;
  cbor_t items[24];
  for (int i = 0; i < 24; i++) items[i] = cbor_v_mk_uint64((uint64_t)i);
  cbor_t expected;
  if (!cbor_v_mk_array(items, 24, &expected)) TFAIL("mk arr");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_arr_three_one_byte_nondet(void) {
  /* [1,2,3] but with array length encoded in 1-byte form. */
  uint8_t bytes[] = { 0x98, 0x03, 0x01, 0x02, 0x03 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t items[3] = { cbor_v_mk_uint64(1), cbor_v_mk_uint64(2), cbor_v_mk_uint64(3) };
  cbor_t expected;
  if (!cbor_v_mk_array(items, 3, &expected)) TFAIL("mk arr");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

static int test_arr_three_two_byte_nondet(void) {
  uint8_t bytes[] = { 0x99, 0x00, 0x03, 0x01, 0x02, 0x03 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t items[3] = { cbor_v_mk_uint64(1), cbor_v_mk_uint64(2), cbor_v_mk_uint64(3) };
  cbor_t expected;
  if (!cbor_v_mk_array(items, 3, &expected)) TFAIL("mk arr");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

static int test_arr_empty_eight_byte_nondet(void) {
  uint8_t bytes[] = { 0x9b, 0,0,0,0,0,0,0,0 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t items[1] = { cbor_v_mk_uint64(0) };
  cbor_t expected;
  if (!cbor_v_mk_array(items, 0, &expected)) TFAIL("mk arr");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* ---------- Major type 5: map ---------- */

static int test_map_two_one_byte_nondet(void) {
  /* {1: 1, 2: 2} with map length encoded in 1-byte form. */
  uint8_t bytes[] = { 0xb8, 0x02, 0x01, 0x01, 0x02, 0x02 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_entry_t entries[2] = {
    cbor_v_mk_map_entry(cbor_v_mk_uint64(1), cbor_v_mk_uint64(1)),
    cbor_v_mk_map_entry(cbor_v_mk_uint64(2), cbor_v_mk_uint64(2)),
  };
  cbor_t expected;
  if (!cbor_v_mk_map(entries, 2, &expected)) TFAIL("mk map");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* {1: 0, "a": 1} — mixed key types, canonical order: int < tstr by length. */
static int test_map_mixed_key_types_canonical(void) {
  uint8_t bytes[] = { 0xa2, 0x01, 0x00, 0x61, 'a', 0x01 };
  static uint8_t a[] = { 'a' };
  cbor_t k_a;
  if (!cbor_v_mk_text_string(a, 1, &k_a)) TFAIL("mk tstr");
  cbor_entry_t entries[2] = {
    cbor_v_mk_map_entry(cbor_v_mk_uint64(1), cbor_v_mk_uint64(0)),
    cbor_v_mk_map_entry(k_a, cbor_v_mk_uint64(1)),
  };
  cbor_t expected;
  if (!cbor_v_mk_map(entries, 2, &expected)) TFAIL("mk map");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* ---------- Major type 6: tagged ---------- */

/* Helper macro: tag+uint(0) round-trip. Tag values chosen to avoid
   semantic decoders in cbor2 (no tag in {0..5, 21..24, 28..30, 32..37,
   55799} is used). */
#define MK_TAG_TEST(name, tag_val, header_bytes...)                          \
  static int test_##name(void) {                                             \
    uint8_t bytes[] = { header_bytes, 0x00 };                                \
    cbor_t payload = cbor_v_mk_uint64(0);                                    \
    cbor_t expected;                                                         \
    if (!cbor_v_mk_tagged((uint64_t)(tag_val), &payload, &expected))         \
      TFAIL("mk tagged");                                                    \
    return run_valid_match(bytes, sizeof(bytes), expected);                  \
  }

MK_TAG_TEST(tag_short_canonical,            6,            0xc6)
MK_TAG_TEST(tag_short_last_canonical,       19,           0xd3)
MK_TAG_TEST(tag_one_byte_first_canonical,   99,           0xd8, 0x63)
MK_TAG_TEST(tag_one_byte_last_canonical,    200,          0xd8, 0xc8)
MK_TAG_TEST(tag_two_byte_first_canonical,   257,          0xd9, 0x01, 0x01)
MK_TAG_TEST(tag_two_byte_last_canonical,    65535,        0xd9, 0xff, 0xff)
MK_TAG_TEST(tag_four_byte_first_canonical,  65536ULL,     0xda, 0x00, 0x01, 0x00, 0x00)
MK_TAG_TEST(tag_four_byte_last_canonical,   0xffffffffULL, 0xda, 0xff, 0xff, 0xff, 0xff)
MK_TAG_TEST(tag_eight_byte_first_canonical, 0x100000000ULL, 0xdb, 0,0,0,1,0,0,0,0)
MK_TAG_TEST(tag_max_canonical,              0xffffffffffffffffULL, 0xdb, 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff)

/* Nested tagged: tag 1234 wrapping tag 5678 wrapping uint 1.
 * 0xd9 0x04 0xd2 (tag 1234)
 * 0xd9 0x16 0x2e (tag 5678)
 * 0x01           (uint 1) */
static int test_tag_nested_canonical(void) {
  uint8_t bytes[] = { 0xd9, 0x04, 0xd2,  0xd9, 0x16, 0x2e,  0x01 };
  cbor_t inner = cbor_v_mk_uint64(1);
  cbor_t mid;
  if (!cbor_v_mk_tagged(5678, &inner, &mid)) TFAIL("mk inner tag");
  cbor_t expected;
  if (!cbor_v_mk_tagged(1234, &mid, &expected)) TFAIL("mk outer tag");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* Tag 99 wrapping array [1, 2, 3]. (Tag 99 chosen to avoid cbor2's
   auto-decoders for tags 0-37, 100, 1004, 55799.) */
static int test_tag_array_payload_canonical(void) {
  uint8_t bytes[] = { 0xd8, 0x63,  0x83, 0x01, 0x02, 0x03 };
  cbor_t items[3] = { cbor_v_mk_uint64(1), cbor_v_mk_uint64(2), cbor_v_mk_uint64(3) };
  cbor_t arr;
  if (!cbor_v_mk_array(items, 3, &arr)) TFAIL("mk arr");
  cbor_t expected;
  if (!cbor_v_mk_tagged(99, &arr, &expected)) TFAIL("mk tag");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* Canonical tag wrapping non-canonical inner uint (24 in 2-byte form).
   Det rejects (inner not canonical); nondet accepts. */
static int test_tag_inner_nondet(void) {
  uint8_t bytes[] = { 0xd9, 0x03, 0xe8,  0x19, 0x00, 0x18 };
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t inner = cbor_v_mk_uint64(24);
  cbor_t expected;
  if (!cbor_v_mk_tagged(1000, &inner, &expected)) TFAIL("mk tagged");
  return run_valid_no_match(bytes, sizeof(bytes), expected);
#endif
}

/* ---------- Major type 7: simple value boundaries ---------- */

static int test_simple_zero_canonical(void) {
  /* Simple value 0: smallest, short-form (0xe0). */
  uint8_t bytes[] = { 0xe0 };
  cbor_t expected;
  if (!cbor_v_mk_simple_value(0, &expected)) TFAIL("mk simple 0");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_simple_19_canonical(void) {
  /* Simple value 19: last short-form value before the assigned
     special values 20 (false), 21 (true), 22 (null), 23 (undefined). */
  uint8_t bytes[] = { 0xf3 };
  cbor_t expected;
  if (!cbor_v_mk_simple_value(19, &expected)) TFAIL("mk simple 19");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_simple_32_canonical(void) {
  /* Simple value 32: smallest value requiring 1-byte arg form. */
  uint8_t bytes[] = { 0xf8, 0x20 };
  cbor_t expected;
  if (!cbor_v_mk_simple_value(32, &expected)) TFAIL("mk simple 32");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_simple_99_canonical(void) {
  uint8_t bytes[] = { 0xf8, 0x63 };
  cbor_t expected;
  if (!cbor_v_mk_simple_value(99, &expected)) TFAIL("mk simple 99");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_simple_254_canonical(void) {
  uint8_t bytes[] = { 0xf8, 0xfe };
  cbor_t expected;
  if (!cbor_v_mk_simple_value(254, &expected)) TFAIL("mk simple 254");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_simple_255_canonical(void) {
  /* Largest simple value. Distinct from the bare 0xff break-stop code
     (which is invalid outside indefinite-length contexts). */
  uint8_t bytes[] = { 0xf8, 0xff };
  cbor_t expected;
  if (!cbor_v_mk_simple_value(255, &expected)) TFAIL("mk simple 255");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

/* Simple-value 1-byte forms with arguments < 32 are forbidden (RFC 8949
   §3.3): they would alias the short-form encodings 0xe0..0xf7 (or in the
   case of 24-31 conflict with the float headers/break stop). */
static int test_simple_25_invalid(void) {
  uint8_t bytes[] = { 0xf8, 0x19 };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_simple_26_invalid(void) {
  uint8_t bytes[] = { 0xf8, 0x1a };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_simple_27_invalid(void) {
  uint8_t bytes[] = { 0xf8, 0x1b };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_simple_28_invalid(void) {
  uint8_t bytes[] = { 0xf8, 0x1c };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_simple_29_invalid(void) {
  uint8_t bytes[] = { 0xf8, 0x1d };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_simple_30_invalid(void) {
  uint8_t bytes[] = { 0xf8, 0x1e };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_simple_31_invalid(void) {
  uint8_t bytes[] = { 0xf8, 0x1f };
  return run_invalid(bytes, sizeof(bytes));
}

/* ---------- Cross-cutting / structural ---------- */

static int test_empty_buffer_invalid(void) {
  /* Validate must reject an empty buffer. */
  uint8_t dummy[1] = { 0x00 };
  return run_invalid(dummy, 0);
}

static int test_trunc_19_invalid(void) {
  /* 0x19 expects a 2-byte argument. Only 1 byte present. */
  uint8_t bytes[] = { 0x19, 0x00 };
  return run_invalid(bytes, sizeof(bytes));
}

static int test_trunc_1a_invalid(void) {
  /* 0x1a expects a 4-byte argument. Only 3 bytes present. */
  uint8_t bytes[] = { 0x1a, 0x00, 0x00, 0x00 };
  return run_invalid(bytes, sizeof(bytes));
}

static int test_trunc_1b_invalid(void) {
  /* 0x1b expects an 8-byte argument. Only 7 bytes present. */
  uint8_t bytes[] = { 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
  return run_invalid(bytes, sizeof(bytes));
}

/* Trailing-byte test: well-formed uint(0) followed by an extra 0xff.
   Validate must succeed (returning the prefix length 1) but the extra
   byte must NOT be consumed. */
static int test_trailing_bytes_canonical(void) {
  uint8_t bytes[] = { 0x00, 0xff };
  cbor_t expected = cbor_v_mk_uint64(0);
  return run_valid_trailing(bytes, sizeof(bytes), 1, expected);
}

static int test_break_stop_alone_invalid(void) {
  /* Bare 0xff (break stop code) outside an indefinite-length context. */
  uint8_t bytes[] = { 0xff };
  return run_invalid(bytes, sizeof(bytes));
}

/* All indefinite-length encodings are unsupported by EverCBOR. */
static int test_indef_bstr_invalid(void) {
  /* Indefinite bstr containing one 0-length bstr chunk. */
  uint8_t bytes[] = { 0x5f, 0x40, 0xff };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_indef_tstr_invalid(void) {
  uint8_t bytes[] = { 0x7f, 0x60, 0xff };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_indef_arr_zero_invalid(void) {
  /* Empty indefinite array. */
  uint8_t bytes[] = { 0x9f, 0xff };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_indef_arr_multi_invalid(void) {
  /* Multi-element indefinite array. */
  uint8_t bytes[] = { 0x9f, 0x01, 0x02, 0x03, 0xff };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_indef_map_invalid(void) {
  /* Indefinite-length map. */
  uint8_t bytes[] = { 0xbf, 0x01, 0x02, 0xff };
  return run_invalid(bytes, sizeof(bytes));
}

/* Reserved additional-info values 0x1c, 0x1d, 0x1e are forbidden in
   every major type that uses an integer argument (0, 1, 4, 5, 6) and
   in major type 7. */
static int test_reserved_uint_1c_invalid(void) {
  uint8_t bytes[] = { 0x1c };  /* major 0, info 28 */
  return run_invalid(bytes, sizeof(bytes));
}
static int test_reserved_uint_1d_invalid(void) {
  uint8_t bytes[] = { 0x1d };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_reserved_uint_1e_invalid(void) {
  uint8_t bytes[] = { 0x1e };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_reserved_negint_3c_invalid(void) {
  uint8_t bytes[] = { 0x3c };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_reserved_arr_9c_invalid(void) {
  uint8_t bytes[] = { 0x9c };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_reserved_map_bc_invalid(void) {
  uint8_t bytes[] = { 0xbc };
  return run_invalid(bytes, sizeof(bytes));
}
static int test_reserved_tag_dc_invalid(void) {
  uint8_t bytes[] = { 0xdc };
  return run_invalid(bytes, sizeof(bytes));
}

/* ============================================================
 *   Test registry & driver
 * ============================================================ */

typedef struct {
  const char *name;
  int (*fn)(void);
} test_entry_t;

static const test_entry_t TESTS[] = {
  /* Major type 0 */
  { "uint_zero_canonical",          test_uint_zero_canonical },
  { "uint_small_canonical",         test_uint_small_canonical },
  { "uint_one_byte_canonical",      test_uint_one_byte_canonical },
  { "uint_two_byte_canonical",      test_uint_two_byte_canonical },
  { "uint_four_byte_canonical",     test_uint_four_byte_canonical },
  { "uint_eight_byte_canonical",    test_uint_eight_byte_canonical },
  { "uint_zero_nondet",             test_uint_zero_nondet },
  { "uint_100_nondet",              test_uint_100_nondet },
  { "uint_zero_long_nondet",        test_uint_zero_long_nondet },

  /* Major type 1 */
  { "neg_minus_one_canonical",      test_neg_minus_one_canonical },
  { "neg_small_canonical",          test_neg_small_canonical },
  { "neg_one_byte_canonical",       test_neg_one_byte_canonical },
  { "neg_minus_one_nondet",         test_neg_minus_one_nondet },

  /* Major type 2 */
  { "bstr_empty_canonical",         test_bstr_empty_canonical },
  { "bstr_short_canonical",         test_bstr_short_canonical },
  { "bstr_empty_nondet",            test_bstr_empty_nondet },

  /* Major type 3 */
  { "tstr_empty_canonical",         test_tstr_empty_canonical },
  { "tstr_hello_canonical",         test_tstr_hello_canonical },
  { "tstr_hello_nondet",            test_tstr_hello_nondet },

  /* Major type 4 */
  { "arr_empty_canonical",          test_arr_empty_canonical },
  { "arr_three_canonical",          test_arr_three_canonical },
  { "arr_empty_nondet",             test_arr_empty_nondet },
  { "arr_deeply_nested_canonical",  test_arr_deeply_nested_canonical },

  /* Major type 5 */
  { "map_empty_canonical",          test_map_empty_canonical },
  { "map_two_canonical",            test_map_two_canonical },
  { "map_two_nondet",               test_map_two_nondet },
  { "map_deeply_nested_canonical",  test_map_deeply_nested_canonical },
  { "map_nested_keys_canonical",    test_map_with_nested_map_keys_canonical },
  { "map_dup_key_invalid",          test_map_dup_key_invalid },
  { "map_dup_diff_enc_invalid",     test_map_dup_key_diff_encoding_invalid },

  /* Major type 6 */
  { "tag_canonical",                test_tag_canonical },
  { "tag_nondet",                   test_tag_nondet },

  /* Major type 7 (no floats) */
  { "simple_short_canonical",       test_simple_short_canonical },
  { "simple_long_canonical",        test_simple_long_canonical },
  { "simple_24_invalid",            test_simple_24_invalid },

  /* General invalid */
  { "invalid_truncated",            test_invalid_truncated },
  { "invalid_bstr_short",           test_invalid_bstr_short },
  { "invalid_arr_short",            test_invalid_arr_short },
  { "invalid_map_short",            test_invalid_map_short },
  { "invalid_indefinite",           test_invalid_indefinite },

  /* ---------- Imported from cbor-test-unverified gentest ---------- */
  { "uint_one_canonical",           test_uint_one_canonical },
  { "uint_ten_canonical",           test_uint_ten_canonical },
  { "uint_24_canonical",            test_uint_24_canonical },
  { "uint_25_canonical",            test_uint_25_canonical },
  { "uint_trillion_canonical",      test_uint_trillion_canonical },
  { "neg_two_byte_canonical",       test_neg_two_byte_canonical },
  { "tstr_a_canonical",             test_tstr_a_canonical },
  { "tstr_ietf_canonical",          test_tstr_ietf_canonical },
  { "tstr_escapes_canonical",       test_tstr_escapes_canonical },
  { "tstr_u_umlaut_canonical",      test_tstr_u_umlaut_canonical },
  { "tstr_water_canonical",         test_tstr_water_canonical },
  { "tstr_drachma_canonical",       test_tstr_drachma_canonical },
  { "arr_nested_canonical",         test_arr_nested_canonical },
  { "arr_25_canonical",             test_arr_25_canonical },
  { "map_mixed_canonical",          test_map_mixed_canonical },
  { "arr_with_map_canonical",       test_arr_with_map_canonical },
  { "map_five_canonical",           test_map_five_canonical },

  /* ---------- UTF-8 (table-driven) ---------- */
#define X(suffix, validity, ...) \
  { "utf8_" #suffix,                test_utf8_##suffix },
  UTF8_TESTS
#undef X

  /* ---------- Recursion-budget tests ---------- */
  { "arr_2200_deep_canonical",      test_arr_2200_deep_canonical },
  { "arr_2200_deep_truncated_invalid", test_arr_2200_deep_truncated_invalid },

  /* ---------- qcbortests ports ---------- */
  { "arr_int_boundaries_canonical", test_arr_int_boundaries_canonical },
  { "arr_empties_canonical",        test_arr_empties_canonical },
  { "map_qcbor_complex_nondet",     test_map_qcbor_complex_nondet },

  /* ---------- New tests for branch coverage ---------- */
  /* Major type 0: integer boundaries */
  { "uint_uint8_max_canonical",            test_uint_uint8_max_canonical },
  { "uint_256_canonical",                  test_uint_256_canonical },
  { "uint_uint16_max_canonical",           test_uint_uint16_max_canonical },
  { "uint_65536_canonical",                test_uint_65536_canonical },
  { "uint_uint32_max_canonical",           test_uint_uint32_max_canonical },
  { "uint_uint64_max_minus_one_canonical", test_uint_uint64_max_minus_one_canonical },
  { "uint_uint64_max_canonical",           test_uint_uint64_max_canonical },
  { "uint_24_two_byte_nondet",             test_uint_24_two_byte_nondet },
  { "uint_24_four_byte_nondet",            test_uint_24_four_byte_nondet },
  { "uint_24_eight_byte_nondet",           test_uint_24_eight_byte_nondet },
  { "uint_uint8_max_two_byte_nondet",      test_uint_uint8_max_two_byte_nondet },
  { "uint_uint16_max_four_byte_nondet",    test_uint_uint16_max_four_byte_nondet },
  /* Major type 1: negint boundaries */
  { "neg_minus_256_canonical",             test_neg_minus_256_canonical },
  { "neg_minus_257_canonical",             test_neg_minus_257_canonical },
  { "neg_minus_65536_canonical",           test_neg_minus_65536_canonical },
  { "neg_minus_65537_canonical",           test_neg_minus_65537_canonical },
  { "neg_minus_2pow32_canonical",          test_neg_minus_2pow32_canonical },
  { "neg_minus_2pow32_minus_one_canonical",test_neg_minus_2pow32_minus_one_canonical },
  { "neg_min_canonical",                   test_neg_min_canonical },
  { "neg_minus_one_two_byte_nondet",       test_neg_minus_one_two_byte_nondet },
  /* Major type 2 */
  { "bstr_23_canonical",                   test_bstr_23_canonical },
  { "bstr_24_canonical",                   test_bstr_24_canonical },
  { "bstr_255_canonical",                  test_bstr_255_canonical },
  { "bstr_256_canonical",                  test_bstr_256_canonical },
  { "bstr_short_two_byte_nondet",          test_bstr_short_two_byte_nondet },
  { "bstr_short_eight_byte_nondet",        test_bstr_short_eight_byte_nondet },
  { "bstr_oversized_invalid",              test_bstr_oversized_invalid },
  /* Major type 3 */
  { "tstr_23_canonical",                   test_tstr_23_canonical },
  { "tstr_24_canonical",                   test_tstr_24_canonical },
  { "tstr_255_canonical",                  test_tstr_255_canonical },
  { "tstr_256_canonical",                  test_tstr_256_canonical },
  { "tstr_a_eight_byte_nondet",            test_tstr_a_eight_byte_nondet },
  { "tstr_oversized_invalid",              test_tstr_oversized_invalid },
  /* Major type 4 */
  { "arr_23_canonical",                    test_arr_23_canonical },
  { "arr_24_canonical",                    test_arr_24_canonical },
  { "arr_three_one_byte_nondet",           test_arr_three_one_byte_nondet },
  { "arr_three_two_byte_nondet",           test_arr_three_two_byte_nondet },
  { "arr_empty_eight_byte_nondet",         test_arr_empty_eight_byte_nondet },
  /* Major type 5 */
  { "map_two_one_byte_nondet",             test_map_two_one_byte_nondet },
  { "map_mixed_key_types_canonical",       test_map_mixed_key_types_canonical },
  /* Major type 6 */
  { "tag_short_canonical",                 test_tag_short_canonical },
  { "tag_short_last_canonical",            test_tag_short_last_canonical },
  { "tag_one_byte_first_canonical",        test_tag_one_byte_first_canonical },
  { "tag_one_byte_last_canonical",         test_tag_one_byte_last_canonical },
  { "tag_two_byte_first_canonical",        test_tag_two_byte_first_canonical },
  { "tag_two_byte_last_canonical",         test_tag_two_byte_last_canonical },
  { "tag_four_byte_first_canonical",       test_tag_four_byte_first_canonical },
  { "tag_four_byte_last_canonical",        test_tag_four_byte_last_canonical },
  { "tag_eight_byte_first_canonical",      test_tag_eight_byte_first_canonical },
  { "tag_max_canonical",                   test_tag_max_canonical },
  { "tag_nested_canonical",                test_tag_nested_canonical },
  { "tag_array_payload_canonical",         test_tag_array_payload_canonical },
  { "tag_inner_nondet",                    test_tag_inner_nondet },
  /* Major type 7: simple values */
  { "simple_zero_canonical",               test_simple_zero_canonical },
  { "simple_19_canonical",                 test_simple_19_canonical },
  { "simple_32_canonical",                 test_simple_32_canonical },
  { "simple_99_canonical",                 test_simple_99_canonical },
  { "simple_254_canonical",                test_simple_254_canonical },
  { "simple_255_canonical",                test_simple_255_canonical },
  { "simple_25_invalid",                   test_simple_25_invalid },
  { "simple_26_invalid",                   test_simple_26_invalid },
  { "simple_27_invalid",                   test_simple_27_invalid },
  { "simple_28_invalid",                   test_simple_28_invalid },
  { "simple_29_invalid",                   test_simple_29_invalid },
  { "simple_30_invalid",                   test_simple_30_invalid },
  { "simple_31_invalid",                   test_simple_31_invalid },
  /* Cross-cutting / structural */
  { "empty_buffer_invalid",                test_empty_buffer_invalid },
  { "trunc_19_invalid",                    test_trunc_19_invalid },
  { "trunc_1a_invalid",                    test_trunc_1a_invalid },
  { "trunc_1b_invalid",                    test_trunc_1b_invalid },
  { "trailing_bytes_canonical",            test_trailing_bytes_canonical },
  { "break_stop_alone_invalid",            test_break_stop_alone_invalid },
  { "indef_bstr_invalid",                  test_indef_bstr_invalid },
  { "indef_tstr_invalid",                  test_indef_tstr_invalid },
  { "indef_arr_zero_invalid",              test_indef_arr_zero_invalid },
  { "indef_arr_multi_invalid",             test_indef_arr_multi_invalid },
  { "indef_map_invalid",                   test_indef_map_invalid },
  { "reserved_uint_1c_invalid",            test_reserved_uint_1c_invalid },
  { "reserved_uint_1d_invalid",            test_reserved_uint_1d_invalid },
  { "reserved_uint_1e_invalid",            test_reserved_uint_1e_invalid },
  { "reserved_negint_3c_invalid",          test_reserved_negint_3c_invalid },
  { "reserved_arr_9c_invalid",             test_reserved_arr_9c_invalid },
  { "reserved_map_bc_invalid",             test_reserved_map_bc_invalid },
  { "reserved_tag_dc_invalid",             test_reserved_tag_dc_invalid },
};

#define N_TESTS ((int)(sizeof(TESTS) / sizeof(TESTS[0])))

int main(void) {
  /* Output directory may be overridden through the environment so that the
   * Makefile/Python harness can choose where to find the artefacts. */
  const char *env_out = getenv("CBOR_TEST_OUT_DIR");
  if (env_out && *env_out) g_out_dir = env_out;
  if (ensure_out_dir() != 0) return 2;

  printf("EverCBOR test suite [%s] : %d tests, %d iterations each\n"
         "Writing artefacts under '%s/'\n",
         API_NAME, N_TESTS, (int)BENCH_ITERATIONS, g_out_dir);

  int passed = 0, failed = 0;
  double total_seconds = 0.0;
  for (int i = 0; i < N_TESTS; i++) {
    printf("[%s] %-36s ", API_NAME, TESTS[i].name);
    fflush(stdout);
    g_current_test = TESTS[i].name;

    /* Warmup pass: run the test once with file-writing enabled so each
     * artefact is materialised exactly once before the timed loop. */
    g_write_files = 1;
    int rc = TESTS[i].fn();
    g_write_files = 0;
    if (rc != 0) {
      printf("FAIL (during artefact warmup)\n");
      failed++;
      continue;
    }

    clock_t start = clock();
    for (int it = 0; it < BENCH_ITERATIONS; it++) {
      rc = TESTS[i].fn();
      if (rc != 0) break;
    }
    clock_t stop = clock();
    double seconds = ((double)(stop - start)) / CLOCKS_PER_SEC;
    total_seconds += seconds;
    if (rc == 0) {
      printf("PASS  %d iters in %.6fs (%.3e s/iter)\n",
             (int)BENCH_ITERATIONS, seconds, seconds / BENCH_ITERATIONS);
      passed++;
    } else {
      printf("FAIL\n");
      failed++;
    }
  }

  printf("\n[%s] Summary: %d/%d passed, %d failed; total time %.6fs\n",
         API_NAME, passed, N_TESTS, failed, total_seconds);
  return failed == 0 ? 0 : 1;
}
