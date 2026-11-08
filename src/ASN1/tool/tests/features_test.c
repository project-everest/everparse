/* Round trip through the C API that everparse-asn1 generates for
   Features.asn: open ranges and unions in constraints, DEFAULT values of
   string and BIT STRING types, DEFINED-BY keys of string and INTEGER
   types, EXTERNAL and EMBEDDED PDV, KEEP-BYTES under an IMPLICIT tag and on
   a component. */
#include "Features.h"
#include <stdio.h>
#include <string.h>
#define BUF 128

static int fails = 0;
#define CHECK(c, ...) do { if (!(c)) { printf(__VA_ARGS__); printf("\n"); fails++; } } while (0)

static Pulse_Lib_Slice_slice__uint8 sl(const char *s) {
  return (Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)s, .len = strlen(s) };
}

static Pulse_Lib_Slice_slice__uint8 bsl(const uint8_t *s, size_t len) {
  return (Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)s, .len = len };
}

static ASN1_Pulse_Rel_asn1_int_impl small(int64_t x) {
  return (ASN1_Pulse_Rel_asn1_int_impl){ .tag = ASN1_PULSE_REL_SMALL, .val = { .Small = x } };
}

static int same(Pulse_Lib_Slice_slice__uint8 s, const uint8_t *exp, size_t len) {
  return s.len == len && memcmp(s.elt, exp, len) == 0;
}

/* Rec { n 5, m -1, kept { a 1, b 'AA'H }, payload { x 7 } },
   all DEFAULT and OPTIONAL components absent */
static Rec rec1(void) {
  Rec r;
  memset(&r, 0, sizeof r);
  r.n = 5;
  r.m = -1;
  r.data.tag = FEATURES_IMPL_REC_DATA_ABSENT;
  r.label_.tag = FEATURES_IMPL_REC_LABEL_ABSENT;
  r.pr.tag = FEATURES_IMPL_REC_PR_ABSENT;
  r.flags.tag = FEATURES_IMPL_REC_FLAGS_ABSENT;
  r.bits.tag = FEATURES_IMPL_REC_BITS_ABSENT;
  r.kept.value.a = small(1);
  r.kept.value.b = bsl((const uint8_t *)"\xaa", 1);
  r.kept.raw.tag = FEATURES_IMPL_BLOB_RAW_ABSENT;
  r.payload.value = small(7);
  r.payload.raw.tag = FEATURES_IMPL_REC_PAYLOAD_RAW_ABSENT;
  r.ext.tag = FEATURES_IMPL_REC_EXT_ABSENT;
  return r;
}

static const uint8_t rec1_der[] = {
  0x30, 0x13,
  0x02, 0x01, 0x05,                                     /* n */
  0x02, 0x01, 0xff,                                     /* m */
  0xa6, 0x06, 0x02, 0x01, 0x01, 0x04, 0x01, 0xaa,       /* kept [6] */
  0x30, 0x03, 0x02, 0x01, 0x07,                         /* payload */
};

static const uint8_t cafe[] = { 0xca, 0xfe };
static const uint8_t beef[] = { 0xbe, 0xef };
static const uint8_t x40[] = { 0x40 };
static const uint8_t x80[] = { 0x80 };
static const uint8_t xa0[] = { 0xa0 };
static const uint8_t xc0[] = { 0xc0 };

/* rec1 with each DEFAULT component present with its default value */
static Rec rec1_defaults(void) {
  Rec r = rec1();
  r.data.tag = FEATURES_IMPL_REC_DATA_PRESENT;
  r.data.val.Rec_data_present = bsl(cafe, 2);
  r.label_.tag = FEATURES_IMPL_REC_LABEL_PRESENT;
  r.label_.val.Rec_label_present = sl("h\xc3\xa9");
  r.pr.tag = FEATURES_IMPL_REC_PR_PRESENT;
  r.pr.val.Rec_pr_present = sl("A B");
  r.flags.tag = FEATURES_IMPL_REC_FLAGS_PRESENT;
  r.flags.val.Rec_flags_present = (ASN1_Pulse_Rel_asn1_bitstring_impl){ .unused = 6, .bytes = bsl(x40, 1) };
  r.bits.tag = FEATURES_IMPL_REC_BITS_PRESENT;
  r.bits.val.Rec_bits_present = (ASN1_Pulse_Rel_asn1_bitstring_impl){ .unused = 5, .bytes = bsl(xa0, 1) };
  return r;
}

static const uint8_t xab[] = { 0xab };

/* Rec { n 9, m 5, data 'BEEF'H, label "x", pr "Z", flags { f0 },
         bits '11'B, kept { a 1, b 'AA'H }, payload { x 7 },
         ext { indirect-reference 3, encoding octet-aligned 'AB'H } } */
static Rec rec2(void) {
  Rec r = rec1();
  r.n = 9;
  r.m = 5;
  r.data.tag = FEATURES_IMPL_REC_DATA_PRESENT;
  r.data.val.Rec_data_present = bsl(beef, 2);
  r.label_.tag = FEATURES_IMPL_REC_LABEL_PRESENT;
  r.label_.val.Rec_label_present = sl("x");
  r.pr.tag = FEATURES_IMPL_REC_PR_PRESENT;
  r.pr.val.Rec_pr_present = sl("Z");
  r.flags.tag = FEATURES_IMPL_REC_FLAGS_PRESENT;
  r.flags.val.Rec_flags_present = (ASN1_Pulse_Rel_asn1_bitstring_impl){ .unused = 7, .bytes = bsl(x80, 1) };
  r.bits.tag = FEATURES_IMPL_REC_BITS_PRESENT;
  r.bits.val.Rec_bits_present = (ASN1_Pulse_Rel_asn1_bitstring_impl){ .unused = 6, .bytes = bsl(xc0, 1) };
  r.ext.tag = FEATURES_IMPL_REC_EXT_PRESENT;
  EXTERNAL_body e;
  memset(&e, 0, sizeof e);
  e.direct_reference.tag = FEATURES_IMPL_EXTERNAL_BODY_DIRECT_REFERENCE_ABSENT;
  e.indirect_reference.tag = FEATURES_IMPL_EXTERNAL_BODY_INDIRECT_REFERENCE_PRESENT;
  e.indirect_reference.val.EXTERNAL_body_indirect_reference_present = small(3);
  e.data_value_descriptor.tag = FEATURES_IMPL_EXTERNAL_BODY_DATA_VALUE_DESCRIPTOR_ABSENT;
  e.encoding.tag = FEATURES_IMPL_EXTERNAL_BODY_ENCODING_OCTET_ALIGNED;
  e.encoding.val.EXTERNAL_body_encoding_octet_aligned = bsl(xab, 1);
  r.ext.val.Rec_ext_present = e;
  return r;
}

static const uint8_t rec2_der[] = {
  0x30, 0x2d,
  0x02, 0x01, 0x09,                                     /* n */
  0x02, 0x01, 0x05,                                     /* m */
  0x04, 0x02, 0xbe, 0xef,                               /* data */
  0x0c, 0x01, 0x78,                                     /* label */
  0x13, 0x01, 0x5a,                                     /* pr */
  0x03, 0x02, 0x07, 0x80,                               /* flags */
  0x85, 0x02, 0x06, 0xc0,                               /* bits [5] */
  0xa6, 0x06, 0x02, 0x01, 0x01, 0x04, 0x01, 0xaa,       /* kept [6] */
  0x30, 0x03, 0x02, 0x01, 0x07,                         /* payload */
  0xa7, 0x06, 0x02, 0x01, 0x03, 0x81, 0x01, 0xab,       /* ext [7] */
};

static int validate_rec(const uint8_t *in, size_t len) {
  size_t off = 0;
  return validate_Rec(bsl(in, len), &off) && off == len;
}

static void rec_write(const char *name, Rec x, const uint8_t *exp, size_t len) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Rec(x, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write: expected the DER bytes (result %d, %zu bytes)", name, (int)r, BUF - pos);
  pos = len - 1;
  Pulse_Lib_Slice_slice__uint8 s = { .elt = out, .len = len - 1 };
  CHECK(write_Rec(x, s, &pos) == ASN1_PULSE_JITWRITER_JIT_NO_SPACE,
        "%s: short buffer: expected NO_SPACE", name);
}

/* validate and parse `in`, check the kept bytes, then write back */
static void rec_parse(const char *name, const uint8_t *in, size_t len, size_t kept_off, size_t payload_off) {
  CHECK(validate_rec(in, len), "%s: validate", name);
  Rec p = parse_Rec(bsl(in, len));
  CHECK(p.kept.raw.tag == FEATURES_IMPL_BLOB_RAW_PRESENT &&
        p.kept.raw.val.Blob_raw_present.elt == in + kept_off &&
        p.kept.raw.val.Blob_raw_present.len == 8, "%s: parse: kept bytes (with the [6] tag)", name);
  CHECK(p.payload.raw.tag == FEATURES_IMPL_REC_PAYLOAD_RAW_PRESENT &&
        p.payload.raw.val.Rec_payload_raw_present.elt == in + payload_off &&
        p.payload.raw.val.Rec_payload_raw_present.len == 5, "%s: parse: payload bytes", name);
  CHECK(p.payload.value.tag == ASN1_PULSE_REL_SMALL && p.payload.value.val.Small == 7, "%s: parse: payload", name);
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Rec_typed(p, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, in, len) == 0,
        "%s: write back", name);
  /* stale kept bytes are ignored by the writer */
  p.kept.raw.val.Blob_raw_present = sl("garbage");
  p.payload.raw.val.Rec_payload_raw_present = sl("junk");
  pos = BUF;
  r = write_Rec(p, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, in, len) == 0,
        "%s: write with stale kept bytes", name);
}

static void rec_invalid(const char *name, Rec x) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Rec(x, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_INVALID, "%s: expected INVALID (%d)", name, (int)r);
}

static void test_rec(void) {
  rec_write("rec1", rec1(), rec1_der, sizeof rec1_der);
  rec_write("rec1 with default values", rec1_defaults(), rec1_der, sizeof rec1_der);
  rec_write("rec2", rec2(), rec2_der, sizeof rec2_der);
  rec_parse("rec1", rec1_der, sizeof rec1_der, 8, 16);
  rec_parse("rec2", rec2_der, sizeof rec2_der, 26, 34);
  Rec p = parse_Rec(bsl(rec2_der, sizeof rec2_der));
  CHECK(p.n == 9 && p.m == 5 && p.data.tag == FEATURES_IMPL_REC_DATA_PRESENT &&
        same(p.data.val.Rec_data_present, beef, 2) &&
        p.label_.tag == FEATURES_IMPL_REC_LABEL_PRESENT &&
        same(p.label_.val.Rec_label_present, (const uint8_t *)"x", 1) &&
        p.flags.tag == FEATURES_IMPL_REC_FLAGS_PRESENT && p.flags.val.Rec_flags_present.unused == 7 &&
        p.bits.tag == FEATURES_IMPL_REC_BITS_PRESENT && p.bits.val.Rec_bits_present.unused == 6 &&
        p.ext.tag == FEATURES_IMPL_REC_EXT_PRESENT &&
        p.ext.val.Rec_ext_present.encoding.tag == FEATURES_IMPL_EXTERNAL_BODY_ENCODING_OCTET_ALIGNED,
        "rec2: parse: values");

  /* n: INTEGER (0<..<10 | 20 | 30..32) */
  static const int64_t n_ok[] = { 1, 9, 20, 30, 32 };
  static const int64_t n_bad[] = { 0, 10, 15, 19, 21, 29, 33, -1 };
  for (size_t i = 0; i < sizeof n_ok / sizeof n_ok[0]; i++) {
    Rec r = rec1();
    r.n = n_ok[i];
    uint8_t exp[sizeof rec1_der];
    memcpy(exp, rec1_der, sizeof exp);
    exp[4] = (uint8_t)n_ok[i];
    char name[32];
    snprintf(name, sizeof name, "n = %d", (int)n_ok[i]);
    rec_write(name, r, exp, sizeof exp);
    CHECK(validate_rec(exp, sizeof exp), "%s: validate", name);
  }
  for (size_t i = 0; i < sizeof n_bad / sizeof n_bad[0]; i++) {
    Rec r = rec1();
    r.n = n_bad[i];
    char name[32];
    snprintf(name, sizeof name, "n = %d", (int)n_bad[i]);
    rec_invalid(name, r);
    uint8_t in[sizeof rec1_der];
    memcpy(in, rec1_der, sizeof in);
    in[4] = (uint8_t)n_bad[i];
    CHECK(!validate_rec(in, sizeof in), "%s: expected rejection", name);
  }
  /* m: INTEGER (-3..<0 | 0<..5) */
  static const int64_t m_ok[] = { -3, -1, 1, 5 };
  static const int64_t m_bad[] = { -4, 0, 6 };
  for (size_t i = 0; i < sizeof m_ok / sizeof m_ok[0]; i++) {
    Rec r = rec1();
    r.m = m_ok[i];
    uint8_t exp[sizeof rec1_der];
    memcpy(exp, rec1_der, sizeof exp);
    exp[7] = (uint8_t)m_ok[i];
    char name[32];
    snprintf(name, sizeof name, "m = %d", (int)m_ok[i]);
    rec_write(name, r, exp, sizeof exp);
  }
  for (size_t i = 0; i < sizeof m_bad / sizeof m_bad[0]; i++) {
    Rec r = rec1();
    r.m = m_bad[i];
    char name[32];
    snprintf(name, sizeof name, "m = %d", (int)m_bad[i]);
    rec_invalid(name, r);
    uint8_t in[sizeof rec1_der];
    memcpy(in, rec1_der, sizeof in);
    in[7] = (uint8_t)m_bad[i];
    CHECK(!validate_rec(in, sizeof in), "%s: expected rejection", name);
  }
  /* data: OCTET STRING (SIZE (1<..4 | 5)) */
  static const uint8_t six[] = { 1, 2, 3, 4, 5, 6 };
  Rec r = rec2();
  r.data.val.Rec_data_present = bsl(six, 1);
  rec_invalid("data: 1 byte", r);
  r.data.val.Rec_data_present = bsl(six, 6);
  rec_invalid("data: 6 bytes", r);
  r.data.val.Rec_data_present = bsl(six, 5);
  {
    uint8_t out[BUF];
    size_t pos = BUF;
    CHECK(write_Rec(r, (Pulse_Lib_Slice_slice__uint8){ .elt = out, .len = BUF }, &pos) == ASN1_PULSE_JITWRITER_JIT_OK,
          "data: 5 bytes: write");
  }
  /* pr: PrintableString */
  r = rec2();
  r.pr.val.Rec_pr_present = sl("a*");
  rec_invalid("pr: not printable", r);
  /* label: UTF8String */
  r = rec2();
  r.label_.val.Rec_label_present = sl("\xc3");
  rec_invalid("label: not UTF-8", r);
  /* flags: the unused bits must be zero */
  static const uint8_t x81[] = { 0x81 };
  r = rec2();
  r.flags.val.Rec_flags_present.bytes = bsl(x81, 1);
  rec_invalid("flags: unused bit set", r);
  r.flags.val.Rec_flags_present.unused = 8;
  rec_invalid("flags: 8 unused bits", r);

  /* DEFAULT values present in the input are rejected */
  static const uint8_t with_data[] = {
    0x30, 0x17, 0x02, 0x01, 0x05, 0x02, 0x01, 0xff,
    0x04, 0x02, 0xca, 0xfe,
    0xa6, 0x06, 0x02, 0x01, 0x01, 0x04, 0x01, 0xaa, 0x30, 0x03, 0x02, 0x01, 0x07,
  };
  CHECK(!validate_rec(with_data, sizeof with_data), "data 'CAFE'H present: expected rejection");
  static const uint8_t with_label[] = {
    0x30, 0x18, 0x02, 0x01, 0x05, 0x02, 0x01, 0xff,
    0x0c, 0x03, 0x68, 0xc3, 0xa9,
    0xa6, 0x06, 0x02, 0x01, 0x01, 0x04, 0x01, 0xaa, 0x30, 0x03, 0x02, 0x01, 0x07,
  };
  CHECK(!validate_rec(with_label, sizeof with_label), "label \"h\\u00e9\" present: expected rejection");
  static const uint8_t with_bits[] = {
    0x30, 0x17, 0x02, 0x01, 0x05, 0x02, 0x01, 0xff,
    0x85, 0x02, 0x05, 0xa0,
    0xa6, 0x06, 0x02, 0x01, 0x01, 0x04, 0x01, 0xaa, 0x30, 0x03, 0x02, 0x01, 0x07,
  };
  CHECK(!validate_rec(with_bits, sizeof with_bits), "bits '101'B present: expected rejection");
  uint8_t in[sizeof with_bits];
  memcpy(in, with_bits, sizeof in);
  in[11] = 0xe0; /* bits '111'B */
  CHECK(validate_rec(in, sizeof in), "bits '111'B present: validate");
}

/* Item: DEFINED BY a UTF8String, FALLBACK NONE */

static int validate_item(const uint8_t *in, size_t len) {
  size_t off = 0;
  return validate_Item(bsl(in, len), &off) && off == len;
}

static void item_ok(const char *name, Item x, const uint8_t *exp, size_t len) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Item(x, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write: expected the DER bytes (result %d, %zu bytes)", name, (int)r, BUF - pos);
  CHECK(validate_item(exp, len), "%s: validate", name);
  Item p = parse_Item(bsl(exp, len));
  CHECK(p.tag == x.tag, "%s: parse", name);
  pos = BUF;
  r = write_Item_typed(p, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write back", name);
}

static const uint8_t item_num[] = { 0x30, 0x08, 0x0c, 0x03, 0x6e, 0x75, 0x6d, 0x02, 0x01, 0x05 };
static const uint8_t item_str[] = { 0x30, 0x09, 0x0c, 0x03, 0x73, 0x74, 0x72, 0x0c, 0x02, 0x61, 0x62 };

static void test_item(void) {
  Item i = { .tag = FEATURES_IMPL_ITEM_KIND_K0, .val = { .Item_kind_k0 = small(5) } };
  item_ok("item num", i, item_num, sizeof item_num);
  i = (Item){ .tag = FEATURES_IMPL_ITEM_KIND_K1, .val = { .Item_kind_k1 = sl("ab") } };
  item_ok("item str", i, item_str, sizeof item_str);
  i.val.Item_kind_k1 = sl("\xff");
  {
    uint8_t out[BUF];
    size_t pos = BUF;
    CHECK(write_Item(i, (Pulse_Lib_Slice_slice__uint8){ .elt = out, .len = BUF }, &pos) == ASN1_PULSE_JITWRITER_JIT_INVALID,
          "item str: not UTF-8: expected INVALID");
  }
  static const uint8_t unknown[] = { 0x30, 0x08, 0x0c, 0x03, 0x66, 0x6f, 0x6f, 0x02, 0x01, 0x05 };
  CHECK(!validate_item(unknown, sizeof unknown), "item: unknown key: expected rejection");
  static const uint8_t mismatch[] = { 0x30, 0x09, 0x0c, 0x03, 0x6e, 0x75, 0x6d, 0x0c, 0x02, 0x61, 0x62 };
  CHECK(!validate_item(mismatch, sizeof mismatch), "item: num with a UTF8String: expected rejection");
}

/* Opt: DEFINED BY an INTEGER, OPTIONAL, with the default fallback */

static int validate_opt(const uint8_t *in, size_t len) {
  size_t off = 0;
  return validate_Opt(bsl(in, len), &off) && off == len;
}

static void opt_ok(const char *name, Opt x, const uint8_t *exp, size_t len) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Opt(x, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write: expected the DER bytes (result %d, %zu bytes)", name, (int)r, BUF - pos);
  CHECK(validate_opt(exp, len), "%s: validate", name);
  Opt p = parse_Opt(bsl(exp, len));
  CHECK(p.tag == x.tag, "%s: parse", name);
  pos = BUF;
  r = write_Opt_typed(p, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write back", name);
}

static const uint8_t opt_bool[] = { 0x30, 0x06, 0x02, 0x01, 0x01, 0x01, 0x01, 0xff };
static const uint8_t opt_null[] = { 0x30, 0x05, 0x02, 0x01, 0x02, 0x05, 0x00 };
static const uint8_t opt_other[] = { 0x30, 0x03, 0x02, 0x01, 0x07 };
static const uint8_t opt_other_val[] = { 0x30, 0x06, 0x02, 0x01, 0x07, 0x04, 0x01, 0xab };

static void test_opt(void) {
  Opt o = { .tag = FEATURES_IMPL_OPT_CODE_K0, .val = { .Opt_code_k0 = true } };
  opt_ok("opt bool", o, opt_bool, sizeof opt_bool);
  o = (Opt){ .tag = FEATURES_IMPL_OPT_CODE_K1 };
  opt_ok("opt null", o, opt_null, sizeof opt_null);
  o = (Opt){ .tag = FEATURES_IMPL_OPT_CODE_OTHER };
  o.val.Opt_code_other.key = small(7);
  o.val.Opt_code_other.other.tag = FEATURES_IMPL_OPT_VAL_ABSENT;
  opt_ok("opt other, absent", o, opt_other, sizeof opt_other);
  CHECK(validate_opt(opt_other_val, sizeof opt_other_val), "opt other, present: validate");
  Opt p = parse_Opt(bsl(opt_other_val, sizeof opt_other_val));
  CHECK(p.tag == FEATURES_IMPL_OPT_CODE_OTHER && p.val.Opt_code_other.key.val.Small == 7 &&
        p.val.Opt_code_other.other.tag == FEATURES_IMPL_OPT_VAL_PRESENT,
        "opt other, present: parse");
  uint8_t out[BUF];
  size_t pos = BUF;
  ASN1_Pulse_JitWriter_jit_result r = write_Opt_typed(p, (Pulse_Lib_Slice_slice__uint8){ .elt = out, .len = BUF }, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - sizeof opt_other_val &&
        memcmp(out + pos, opt_other_val, sizeof opt_other_val) == 0, "opt other, present: write back");
  /* a known key with another type */
  static const uint8_t mismatch[] = { 0x30, 0x05, 0x02, 0x01, 0x01, 0x05, 0x00 };
  CHECK(!validate_opt(mismatch, sizeof mismatch), "opt: 1 with a NULL: expected rejection");
}

/* Pdv: EMBEDDED PDV */

static int validate_pdv(const uint8_t *in, size_t len) {
  size_t off = 0;
  return validate_Pdv(bsl(in, len), &off) && off == len;
}

static void pdv_ok(const char *name, EMBEDDED_PDV_body x, const uint8_t *exp, size_t len) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Pdv(x, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write: expected the DER bytes (result %d, %zu bytes)", name, (int)r, BUF - pos);
  CHECK(validate_pdv(exp, len), "%s: validate", name);
  EMBEDDED_PDV_body p = parse_Pdv(bsl(exp, len));
  CHECK(p.identification.tag == x.identification.tag && same(p.data_value, x.data_value.elt, x.data_value.len),
        "%s: parse", name);
  pos = BUF;
  r = write_Pdv_typed(p, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write back", name);
}

/* { identification fixed, data-value 'hi' } */
static const uint8_t pdv_fixed[] = { 0x2b, 0x08, 0xa0, 0x02, 0x85, 0x00, 0x82, 0x02, 0x68, 0x69 };
/* { identification syntax { 1 2 3 }, data-value 'hi' } */
static const uint8_t pdv_syntax[] = { 0x2b, 0x0a, 0xa0, 0x04, 0x81, 0x02, 0x2a, 0x03, 0x82, 0x02, 0x68, 0x69 };
static const uint8_t oid123[] = { 0x2a, 0x03 };

static void test_pdv(void) {
  EMBEDDED_PDV_body x;
  memset(&x, 0, sizeof x);
  x.identification.tag = FEATURES_IMPL_UNIVERSAL_IDENTIFICATION_FIXED;
  x.data_value = sl("hi");
  pdv_ok("pdv fixed", x, pdv_fixed, sizeof pdv_fixed);
  x.identification.tag = FEATURES_IMPL_UNIVERSAL_IDENTIFICATION_SYNTAX;
  x.identification.val.UNIVERSAL_Identification_syntax = bsl(oid123, 2);
  pdv_ok("pdv syntax", x, pdv_syntax, sizeof pdv_syntax);
  uint8_t in[sizeof pdv_fixed];
  memcpy(in, pdv_fixed, sizeof in);
  in[0] = 0x30; /* SEQUENCE instead of [UNIVERSAL 11] */
  CHECK(!validate_pdv(in, sizeof in), "pdv: wrong tag: expected rejection");
}

int main(void) {
  test_rec();
  test_item();
  test_opt();
  test_pdv();
  if (fails) {
    printf("features_test: %d failure(s)\n", fails);
    return 1;
  }
  printf("features_test: OK\n");
  return 0;
}
