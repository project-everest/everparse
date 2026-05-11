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

/* For valid encodings: validate, parse, compare with `expected`,
 * serialize `expected`, validate+parse the output, compare again.
 * If `match_bytes`, also assert the serialized output equals `bytes`.
 */
static int do_run_valid(uint8_t *bytes, size_t len, cbor_t expected,
                        bool match_bytes) {
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

static int test_tag_canonical(void) {
  uint8_t bytes[] = { 0xc1, 0x00 }; /* tag 1, payload uint 0 */
  cbor_t payload = cbor_v_mk_uint64(0);
  cbor_t expected;
  if (!cbor_v_mk_tagged(1, &payload, &expected)) TFAIL("mk tagged");
  if (cbor_v_major_type(expected) != CBOR_MAJOR_TYPE_TAGGED) TFAIL("major");
  cbor_t got_payload;
  uint64_t got_tag;
  if (!cbor_v_get_tagged(expected, &got_payload, &got_tag))
    TFAIL("get tagged");
  if (got_tag != 1) TFAIL("tag value");
  uint64_t pv;
  if (!cbor_v_read_uint64(got_payload, &pv) || pv != 0) TFAIL("payload");
  return run_valid_match(bytes, sizeof(bytes), expected);
}

static int test_tag_nondet(void) {
  uint8_t bytes[] = { 0xd8, 0x01, 0x00 }; /* tag 1 with 1-byte arg */
#if IS_DETERMINISTIC
  return run_invalid(bytes, sizeof(bytes));
#else
  cbor_t payload = cbor_v_mk_uint64(0);
  cbor_t expected;
  if (!cbor_v_mk_tagged(1, &payload, &expected)) TFAIL("mk tagged");
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
};

#define N_TESTS ((int)(sizeof(TESTS) / sizeof(TESTS[0])))

int main(void) {
  printf("EverCBOR test suite [%s] : %d tests, %d iterations each\n",
         API_NAME, N_TESTS, (int)BENCH_ITERATIONS);

  int passed = 0, failed = 0;
  double total_seconds = 0.0;
  for (int i = 0; i < N_TESTS; i++) {
    printf("[%s] %-36s ", API_NAME, TESTS[i].name);
    fflush(stdout);
    int rc = 0;
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
