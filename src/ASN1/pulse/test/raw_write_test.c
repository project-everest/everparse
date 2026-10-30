/* Test of the extracted checked raw writers (ASN1.Pulse.RawWriteTest): raw
   values built in C, with no precondition on their contents, are written
   as is, then the written bytes are validated against the schema. Check
   CW_OK with the expected DER bytes, CW_INVALID on values that are not
   DER encodings of the schema (invalid strings, non-minimal INTEGERs, bad
   BIT STRING padding, DEFAULT values, restrictions, etc.), and CW_NO_SPACE
   on a short buffer. The components of a SET and the elements of a SET OF
   are sorted while writing, whatever their order in the schema or in the
   input. */
#include "ASN1.Pulse.RawWriteTest.h"
#include <stdio.h>
#include <string.h>
#define SL(a) ((Pulse_Lib_Slice_slice__uint8){ .elt = (a), .len = sizeof(a) })
#define BUF 64
#define V(...) { __VA_ARGS__ }

static int fails = 0;

static const char *res_name(ASN1_Pulse_CheckedWriter_cw_result r) {
  switch (r) {
    case ASN1_PULSE_CHECKEDWRITER_CW_OK: return "OK";
    case ASN1_PULSE_CHECKEDWRITER_CW_NO_SPACE: return "NO_SPACE";
    default: return "INVALID";
  }
}

/* Write `x` at the right edge of a BUF-byte buffer. On CW_OK, compare with
   `vec`; then retry with a buffer one byte too short and expect CW_NO_SPACE.
   Check that nothing is written left of the final position. */
#define OK(name, x, vec) do {                                                 \
    uint8_t exp_[] = vec;                                                     \
    uint8_t out_[BUF + 1];                                                    \
    memset(out_, 0xcc, sizeof(out_));                                         \
    size_t pos_ = BUF;                                                        \
    Pulse_Lib_Slice_slice__uint8 o_ = { .elt = out_ + 1, .len = BUF };        \
    ASN1_Pulse_CheckedWriter_cw_result r_ =                                   \
      ASN1_Pulse_RawWriteTest_check_write_raw_##name(x, o_, &pos_);           \
    if (r_ != ASN1_PULSE_CHECKEDWRITER_CW_OK || pos_ != BUF - sizeof(exp_)    \
        || memcmp(out_ + 1 + pos_, exp_, sizeof(exp_)) != 0) {                \
      printf("%s:%d: %s: expected OK, got %s:", __FILE__, __LINE__, #name, res_name(r_)); \
      for (size_t i_ = pos_; i_ < BUF; i_++) printf(" %02x", out_[1 + i_]);   \
      printf("\n"); fails++;                                                  \
    }                                                                         \
    for (size_t i_ = 0; i_ < 1 + pos_ && i_ <= BUF; i_++)                     \
      if (out_[i_] != 0xcc) { printf("%s:%d: %s: wrote left of pos\n", __FILE__, __LINE__, #name); fails++; break; } \
    memset(out_, 0xcc, sizeof(out_));                                         \
    pos_ = sizeof(exp_) - 1;                                                  \
    Pulse_Lib_Slice_slice__uint8 s_ = { .elt = out_ + 1, .len = sizeof(exp_) - 1 }; \
    r_ = ASN1_Pulse_RawWriteTest_check_write_raw_##name(x, s_, &pos_);        \
    if (r_ != ASN1_PULSE_CHECKEDWRITER_CW_NO_SPACE || out_[0] != 0xcc) {      \
      printf("%s:%d: %s: short buffer: expected NO_SPACE, got %s\n", __FILE__, __LINE__, #name, res_name(r_)); fails++; \
    }                                                                         \
  } while (0)

#define INVALID(name, x) do {                                                 \
    uint8_t out_[BUF];                                                        \
    size_t pos_ = BUF;                                                        \
    Pulse_Lib_Slice_slice__uint8 o_ = { .elt = out_, .len = BUF };            \
    ASN1_Pulse_CheckedWriter_cw_result r_ =                                   \
      ASN1_Pulse_RawWriteTest_check_write_raw_##name(x, o_, &pos_);           \
    if (r_ != ASN1_PULSE_CHECKEDWRITER_CW_INVALID) {                          \
      printf("%s:%d: %s: expected INVALID, got %s\n", __FILE__, __LINE__, #name, res_name(r_)); fails++; \
    }                                                                         \
  } while (0)

#define SMALL(n) ((ASN1_Pulse_Rel_asn1_int_impl){ .tag = ASN1_PULSE_REL_SMALL, .val = { .Small = (n) } })
#define NONE_INT ((FStar_Pervasives_Native_option__asn1_int_impl){ .tag = FSTAR_PERVASIVES_NATIVE_NONE__ASN1_INT_IMPL })
#define SOME_INT(n) ((FStar_Pervasives_Native_option__asn1_int_impl){ .tag = FSTAR_PERVASIVES_NATIVE_SOME__ASN1_INT_IMPL, .val = { .Some = SMALL(n) } })
#define NONE_SL ((FStar_Pervasives_Native_option__slice_uint8){ .tag = FSTAR_PERVASIVES_NATIVE_NONE__SLICE_UINT8 })
#define SOME_SL(s) ((FStar_Pervasives_Native_option__slice_uint8){ .tag = FSTAR_PERVASIVES_NATIVE_SOME__SLICE_UINT8, .val = { .Some = (s) } })

typedef FStar_Pervasives_Native_tuple2__option_asn1_int_impl_tuple2_option_slice_uint8_t defL_t;
typedef FStar_Pervasives_Native_option__asn1_int_impl oint;
typedef FStar_Pervasives_Native_option__slice_uint8 osl;

/* SEQUENCE { a INTEGER DEFAULT 0, b OCTET STRING DEFAULT 'ABCD'H,
   s PrintableString DEFAULT "ab", t [0] INTEGER DEFAULT 5,
   r [1] IMPLICIT INTEGER (0..10) DEFAULT 3 } */
static defL_t defL(oint a, osl b, osl s, oint t, oint r) {
  return (defL_t){ ._1 = a, ._2 = { ._1 = b, ._2 = { ._1 = s, ._2 = { ._1 = t, ._2 = r } } } };
}

typedef FStar_Pervasives_Native_tuple2__slice_uint8_tuple2_asn1_int_impl_int64 tagS_t;

/* SEQUENCE { i [0] IMPLICIT IA5String, r INTEGER (0..10), s INTEGER (-128..127) } */
static tagS_t tagS(Pulse_Lib_Slice_slice__uint8 i, int64_t r, int64_t s) {
  return (tagS_t){ ._1 = i, ._2 = { ._1 = SMALL(r), ._2 = s } };
}

typedef LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_asn1_int_impl ints_t;

static ints_t ints(ASN1_Pulse_Rel_asn1_int_impl *a, size_t n) {
  ints_t l = { .tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_BASE__UINTSIZE_ASN1_INT_IMPL };
  if (n == 0)
    l.val.Base.tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_EMPTY__UINTSIZE_ASN1_INT_IMPL;
  else {
    l.val.Base.tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_SLICE__UINTSIZE_ASN1_INT_IMPL;
    l.val.Base.val.Slice.ss = (Pulse_Lib_Slice_slice__asn1_int_impl){ .elt = a, .len = n };
    l.val.Base.val.Slice.count = n;
  }
  return l;
}

typedef LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 octs_t;

static octs_t octs(Pulse_Lib_Slice_slice__uint8 *a, size_t n) {
  octs_t l = { .tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_BASE__UINTSIZE_SLICE_UINT8 };
  if (n == 0)
    l.val.Base.tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_EMPTY__UINTSIZE_SLICE_UINT8;
  else {
    l.val.Base.tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_SLICE__UINTSIZE_SLICE_UINT8;
    l.val.Base.val.Slice.ss = (Pulse_Lib_Slice_slice__slice_uint8){ .elt = a, .len = n };
    l.val.Base.val.Slice.count = n;
  }
  return l;
}

#define BIG(s) ((ASN1_Pulse_Rel_asn1_int_impl){ .tag = ASN1_PULSE_REL_BIG, .val = { .Big = (s) } })
#define SOME_BIG(s) ((FStar_Pervasives_Native_option__asn1_int_impl){ .tag = FSTAR_PERVASIVES_NATIVE_SOME__ASN1_INT_IMPL, .val = { .Some = BIG(s) } })
#define BITS(u, s) ((ASN1_Pulse_Rel_asn1_bitstring_impl){ .unused = (u), .bytes = (s) })
#define INL(i) ((FStar_Pervasives_either__asn1_int_impl_slice_uint8){ .tag = FSTAR_PERVASIVES_INL__ASN1_INT_IMPL_SLICE_UINT8, .val = { .Inl = (i) } })
#define INR(s) ((FStar_Pervasives_either__asn1_int_impl_slice_uint8){ .tag = FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_SLICE_UINT8, .val = { .Inr = (s) } })
#define NONE_B ((FStar_Pervasives_Native_option__bool){ .tag = FSTAR_PERVASIVES_NATIVE_NONE__BOOL })
#define SOME_B(b) ((FStar_Pervasives_Native_option__bool){ .tag = FSTAR_PERVASIVES_NATIVE_SOME__BOOL, .val = { .Some = (b) } })

static octs_t octs_ser(uint8_t *payload, size_t len, size_t count) {
  octs_t l = { .tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_BASE__UINTSIZE_SLICE_UINT8 };
  l.val.Base.tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_SERIALIZED__UINTSIZE_SLICE_UINT8;
  l.val.Base.val.Serialized.count = count;
  l.val.Base.val.Serialized.payload = (Pulse_Lib_Slice_slice__uint8){ .elt = payload, .len = len };
  return l;
}

typedef FStar_Pervasives_Native_tuple2__slice_uint8_tuple2_slice_uint8_tuple2_asn1_bitst mix_t;

/* SEQUENCE { p PrintableString, a ANY, bs BIT STRING, n INTEGER,
   c CHOICE { i INTEGER, o OCTET STRING }, t UTCTime OPTIONAL,
   b BOOLEAN DEFAULT FALSE } */
static mix_t mix(Pulse_Lib_Slice_slice__uint8 p, Pulse_Lib_Slice_slice__uint8 a, ASN1_Pulse_Rel_asn1_bitstring_impl bs,
                 ASN1_Pulse_Rel_asn1_int_impl n, FStar_Pervasives_either__asn1_int_impl_slice_uint8 c,
                 osl t, FStar_Pervasives_Native_option__bool b) {
  return (mix_t){ ._1 = p, ._2 = { ._1 = a, ._2 = { ._1 = bs, ._2 = { ._1 = n, ._2 = { ._1 = c, ._2 = { ._1 = t, ._2 = b } } } } } };
}

typedef FStar_Pervasives_Native_tuple2__slice_uint8_tuple2_option_asn1_int_impl_option_a setCAB_t;

/* SET { c [1] IMPLICIT OCTET STRING, a [0] IMPLICIT INTEGER OPTIONAL,
   b INTEGER DEFAULT 0 } */
static setCAB_t setCAB(Pulse_Lib_Slice_slice__uint8 c, oint a, oint b) {
  return (setCAB_t){ ._1 = c, ._2 = { ._1 = a, ._2 = b } };
}

int main(void) {
  uint8_t ab[] = { 'a', 'b' }, ac[] = { 'a', 'c' }, abcd[] = { 0xab, 0xcd }, abce[] = { 0xab, 0xce };
  uint8_t hi[] = { 'h', 'i' }, hi80[] = { 'h', 0x80 }, hat[] = { 'h', '@' };
  uint8_t aa[] = { 0xaa }, aa00[] = { 0xaa, 0x00 }, f0[] = { 0xf0 }, ff[] = { 0xff }, one[] = { 0x01 };
  uint8_t i256[] = { 0x01, 0x00 }, i128[] = { 0x00, 0x80 }, nm1[] = { 0x00, 0x01 }, nm2[] = { 0xff, 0x80 };
  uint8_t null_[] = { 0x05, 0x00 }, int5[] = { 0x02, 0x01, 0x05 }, badint[] = { 0x02, 0x00 };
  uint8_t utc[] = { '2', '5', '0', '1', '0', '1', '0', '0', '0', '0', '0', '0', 'Z' }, notutc[] = { 'x' };
  uint8_t empty[1];
  Pulse_Lib_Slice_slice__uint8 none = { .elt = empty, .len = 0 };

  /* defL: DEFAULT components, big INTEGERs */
  OK(defL, defL(NONE_INT, NONE_SL, NONE_SL, NONE_INT, NONE_INT), V(0x30, 0x00));
  OK(defL, defL(SOME_INT(1), SOME_SL(SL(abce)), SOME_SL(SL(ac)), SOME_INT(6), SOME_INT(4)),
     V(0x30, 0x13, 0x02, 0x01, 0x01, 0x04, 0x02, 0xab, 0xce, 0x13, 0x02, 'a', 'c',
       0xa0, 0x03, 0x02, 0x01, 0x06, 0x81, 0x01, 0x04));
  OK(defL, defL(SOME_BIG(SL(i256)), NONE_SL, NONE_SL, NONE_INT, NONE_INT), V(0x30, 0x04, 0x02, 0x02, 0x01, 0x00));
  INVALID(defL, defL(SOME_INT(0), NONE_SL, NONE_SL, NONE_INT, NONE_INT));   /* a = default */
  INVALID(defL, defL(NONE_INT, SOME_SL(SL(abcd)), NONE_SL, NONE_INT, NONE_INT)); /* b = default */
  INVALID(defL, defL(NONE_INT, NONE_SL, SOME_SL(SL(ab)), NONE_INT, NONE_INT)); /* s = default */
  INVALID(defL, defL(NONE_INT, NONE_SL, NONE_SL, SOME_INT(5), NONE_INT));   /* t = default */
  INVALID(defL, defL(NONE_INT, NONE_SL, NONE_SL, NONE_INT, SOME_INT(3)));   /* r = default */
  INVALID(defL, defL(NONE_INT, NONE_SL, NONE_SL, NONE_INT, SOME_INT(11)));  /* r > 10 */
  INVALID(defL, defL(NONE_INT, NONE_SL, NONE_SL, NONE_INT, SOME_INT(-1)));  /* r < 0 */
  INVALID(defL, defL(SOME_BIG(SL(nm1)), NONE_SL, NONE_SL, NONE_INT, NONE_INT)); /* non-minimal */
  INVALID(defL, defL(SOME_BIG(none), NONE_SL, NONE_SL, NONE_INT, NONE_INT));    /* empty INTEGER */
  INVALID(defL, defL(NONE_INT, NONE_SL, SOME_SL(SL(hat)), NONE_INT, NONE_INT)); /* not printable */

  /* tagS: restriction, implicitly tagged IA5String, 1-byte INTEGER */
  OK(tagS, tagS(SL(hi), 10, -128), V(0x30, 0x0a, 0x80, 0x02, 'h', 'i', 0x02, 0x01, 0x0a, 0x02, 0x01, 0x80));
  INVALID(tagS, tagS(SL(hi), 11, 0));     /* r > 10 */
  INVALID(tagS, tagS(SL(hi80), 0, 0));    /* not IA5 */
  INVALID(tagS, tagS(SL(hi), 0, 200));    /* s out of 1-byte bound */
  INVALID(tagS, tagS(SL(hi), 0, -129));

  /* neSeqOfInt: SIZE (1..MAX), big INTEGERs */
  {
    ASN1_Pulse_Rel_asn1_int_impl xs[] = { SMALL(5), SMALL(-1), BIG(SL(i128)) };
    ASN1_Pulse_Rel_asn1_int_impl bad[] = { SMALL(5), BIG(SL(nm2)) };
    OK(neSeqOfInt, ints(xs, 3), V(0x30, 0x0a, 0x02, 0x01, 0x05, 0x02, 0x01, 0xff, 0x02, 0x02, 0x00, 0x80));
    INVALID(neSeqOfInt, ints(xs, 0));
    INVALID(neSeqOfInt, ints(bad, 2));    /* non-minimal */
  }

  /* setOfOctets: the elements are sorted by encoding while writing,
     whether structured or serialized; duplicates are allowed */
  {
    uint8_t bb[] = { 0xbb };
    Pulse_Lib_Slice_slice__uint8 sorted[] = { SL(aa), SL(aa00) };
    Pulse_Lib_Slice_slice__uint8 unsorted[] = { SL(aa00), SL(aa) };
    Pulse_Lib_Slice_slice__uint8 three[] = { SL(bb), SL(aa00), SL(aa) };
    Pulse_Lib_Slice_slice__uint8 dup[] = { SL(aa), SL(bb), SL(aa) };
    uint8_t ser_sorted[] = { 0x04, 0x01, 0xaa, 0x04, 0x02, 0xaa, 0x00 };
    uint8_t ser_unsorted[] = { 0x04, 0x02, 0xaa, 0x00, 0x04, 0x01, 0xaa };
    uint8_t ser_bad[] = { 0x04, 0x01, 0xaa, 0x02, 0x00 };
    OK(setOfOctets, octs(sorted, 2), V(0x31, 0x07, 0x04, 0x01, 0xaa, 0x04, 0x02, 0xaa, 0x00));
    OK(setOfOctets, octs(sorted, 0), V(0x31, 0x00));
    OK(setOfOctets, octs_ser(ser_sorted, sizeof(ser_sorted), 2), V(0x31, 0x07, 0x04, 0x01, 0xaa, 0x04, 0x02, 0xaa, 0x00));
    OK(setOfOctets, octs(unsorted, 2), V(0x31, 0x07, 0x04, 0x01, 0xaa, 0x04, 0x02, 0xaa, 0x00));
    OK(setOfOctets, octs_ser(ser_unsorted, sizeof(ser_unsorted), 2), V(0x31, 0x07, 0x04, 0x01, 0xaa, 0x04, 0x02, 0xaa, 0x00));
    OK(setOfOctets, octs(three, 3), V(0x31, 0x0a, 0x04, 0x01, 0xaa, 0x04, 0x01, 0xbb, 0x04, 0x02, 0xaa, 0x00));
    OK(setOfOctets, octs(dup, 3), V(0x31, 0x09, 0x04, 0x01, 0xaa, 0x04, 0x01, 0xaa, 0x04, 0x01, 0xbb));
    INVALID(setOfOctets, octs_ser(ser_bad, sizeof(ser_bad), 2));   /* INTEGER element */
  }

  /* setCAB: the components are sorted by tag while writing, although the
     schema declares them in the reverse order */
  OK(setCAB, setCAB(SL(abcd), SOME_INT(7), SOME_INT(-1)),
     V(0x31, 0x0a, 0x02, 0x01, 0xff, 0x80, 0x01, 0x07, 0x81, 0x02, 0xab, 0xcd));
  OK(setCAB, setCAB(SL(abcd), NONE_INT, NONE_INT), V(0x31, 0x04, 0x81, 0x02, 0xab, 0xcd));
  OK(setCAB, setCAB(SL(abcd), NONE_INT, SOME_INT(-1)), V(0x31, 0x07, 0x02, 0x01, 0xff, 0x81, 0x02, 0xab, 0xcd));
  OK(setCAB, setCAB(none, SOME_INT(7), NONE_INT), V(0x31, 0x05, 0x80, 0x01, 0x07, 0x81, 0x00));
  INVALID(setCAB, setCAB(SL(abcd), NONE_INT, SOME_INT(0)));   /* b = default */
  INVALID(setCAB, setCAB(SL(abcd), SOME_BIG(SL(nm1)), NONE_INT)); /* non-minimal */

  /* mix: strings, ANY, BIT STRING, big INTEGER, CHOICE, OPTIONAL, BOOLEAN DEFAULT */
  OK(mix, mix(SL(hi), SL(null_), BITS(0, SL(aa)), SMALL(300), INL(SMALL(1)), NONE_SL, NONE_B),
     V(0x30, 0x11, 0x13, 0x02, 'h', 'i', 0x05, 0x00, 0x03, 0x02, 0x00, 0xaa,
       0x02, 0x02, 0x01, 0x2c, 0x02, 0x01, 0x01));
  OK(mix, mix(SL(hi), SL(int5), BITS(4, SL(f0)), BIG(SL(i128)), INR(SL(one)), SOME_SL(SL(utc)), SOME_B(true)),
     V(0x30, 0x24, 0x13, 0x02, 'h', 'i', 0x02, 0x01, 0x05, 0x03, 0x02, 0x04, 0xf0,
       0x02, 0x02, 0x00, 0x80, 0x04, 0x01, 0x01,
       0x17, 0x0d, '2', '5', '0', '1', '0', '1', '0', '0', '0', '0', '0', '0', 'Z',
       0x01, 0x01, 0xff));
  OK(mix, mix(SL(hi), SL(null_), BITS(0, none), SMALL(0), INL(SMALL(1)), NONE_SL, NONE_B),
     V(0x30, 0x0f, 0x13, 0x02, 'h', 'i', 0x05, 0x00, 0x03, 0x01, 0x00,
       0x02, 0x01, 0x00, 0x02, 0x01, 0x01));
  INVALID(mix, mix(SL(hat), SL(null_), BITS(0, SL(aa)), SMALL(0), INL(SMALL(1)), NONE_SL, NONE_B));     /* not printable */
  INVALID(mix, mix(SL(hi), SL(badint), BITS(0, SL(aa)), SMALL(0), INL(SMALL(1)), NONE_SL, NONE_B));    /* bad ANY */
  INVALID(mix, mix(SL(hi), none, BITS(0, SL(aa)), SMALL(0), INL(SMALL(1)), NONE_SL, NONE_B));          /* empty ANY */
  INVALID(mix, mix(SL(hi), SL(null_), BITS(8, SL(aa)), SMALL(0), INL(SMALL(1)), NONE_SL, NONE_B));     /* unused > 7 */
  INVALID(mix, mix(SL(hi), SL(null_), BITS(1, SL(ff)), SMALL(0), INL(SMALL(1)), NONE_SL, NONE_B));     /* padding bit set */
  INVALID(mix, mix(SL(hi), SL(null_), BITS(1, none), SMALL(0), INL(SMALL(1)), NONE_SL, NONE_B));       /* unused bits, no bytes */
  INVALID(mix, mix(SL(hi), SL(null_), BITS(0, SL(aa)), BIG(SL(nm1)), INL(SMALL(1)), NONE_SL, NONE_B)); /* non-minimal */
  INVALID(mix, mix(SL(hi), SL(null_), BITS(0, SL(aa)), SMALL(0), INL(BIG(SL(nm2))), NONE_SL, NONE_B)); /* non-minimal */
  INVALID(mix, mix(SL(hi), SL(null_), BITS(0, SL(aa)), SMALL(0), INL(SMALL(1)), SOME_SL(SL(notutc)), NONE_B)); /* bad UTCTime */
  INVALID(mix, mix(SL(hi), SL(null_), BITS(0, SL(aa)), SMALL(0), INL(SMALL(1)), NONE_SL, SOME_B(false))); /* b = default */

  printf(fails ? "FAIL\n" : "OK\n");
  return fails;
}
