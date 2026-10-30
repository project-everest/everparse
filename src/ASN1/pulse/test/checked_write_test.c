/* Test of the extracted checked writers (ASN1.Pulse.CheckedWriteTest): values
   built in C are written with the writer of the relaxed schema, then the
   written bytes are validated against the original schema. Check CW_OK with
   the expected DER bytes, CW_INVALID on values violating a constraint that
   the relaxed schema drops, and CW_NO_SPACE on a short buffer. */
#include "ASN1.Pulse.CheckedWriteTest.h"
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
      ASN1_Pulse_CheckedWriteTest_check_write_##name(x, o_, &pos_);           \
    if (r_ != ASN1_PULSE_CHECKEDWRITER_CW_OK || pos_ != BUF - sizeof(exp_)    \
        || memcmp(out_ + 1 + pos_, exp_, sizeof(exp_)) != 0) {                \
      printf("%s:%d: %s: expected OK, got %s\n", __FILE__, __LINE__, #name, res_name(r_)); fails++; \
    }                                                                         \
    for (size_t i_ = 0; i_ < 1 + pos_ && i_ <= BUF; i_++)                     \
      if (out_[i_] != 0xcc) { printf("%s:%d: %s: wrote left of pos\n", __FILE__, __LINE__, #name); fails++; break; } \
    memset(out_, 0xcc, sizeof(out_));                                         \
    pos_ = sizeof(exp_) - 1;                                                  \
    Pulse_Lib_Slice_slice__uint8 s_ = { .elt = out_ + 1, .len = sizeof(exp_) - 1 }; \
    r_ = ASN1_Pulse_CheckedWriteTest_check_write_##name(x, s_, &pos_);        \
    if (r_ != ASN1_PULSE_CHECKEDWRITER_CW_NO_SPACE || out_[0] != 0xcc) {      \
      printf("%s:%d: %s: short buffer: expected NO_SPACE, got %s\n", __FILE__, __LINE__, #name, res_name(r_)); fails++; \
    }                                                                         \
  } while (0)

#define INVALID(name, x) do {                                                 \
    uint8_t out_[BUF];                                                        \
    size_t pos_ = BUF;                                                        \
    Pulse_Lib_Slice_slice__uint8 o_ = { .elt = out_, .len = BUF };            \
    ASN1_Pulse_CheckedWriter_cw_result r_ =                                   \
      ASN1_Pulse_CheckedWriteTest_check_write_##name(x, o_, &pos_);           \
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

typedef FStar_Pervasives_Native_tuple2__option_asn1_int_impl_tuple2_option_asn1_int_impl setBAC_t;

/* SET { b INTEGER DEFAULT 0, a [0] IMPLICIT INTEGER OPTIONAL, c [1] IMPLICIT OCTET STRING } */
static setBAC_t setBAC(oint b, oint a, Pulse_Lib_Slice_slice__uint8 c) {
  return (setBAC_t){ ._1 = b, ._2 = { ._1 = a, ._2 = c } };
}

int main(void) {
  uint8_t ab[] = { 'a', 'b' }, ac[] = { 'a', 'c' }, abcd[] = { 0xab, 0xcd }, abce[] = { 0xab, 0xce };
  uint8_t hi[] = { 'h', 'i' }, hi80[] = { 'h', 0x80 };
  uint8_t aa[] = { 0xaa }, aa00[] = { 0xaa, 0x00 };

  /* defL: DEFAULT components */
  OK(defL, defL(NONE_INT, NONE_SL, NONE_SL, NONE_INT, NONE_INT), V(0x30, 0x00));
  OK(defL, defL(SOME_INT(1), SOME_SL(SL(abce)), SOME_SL(SL(ac)), SOME_INT(6), SOME_INT(4)),
     V(0x30, 0x13, 0x02, 0x01, 0x01, 0x04, 0x02, 0xab, 0xce, 0x13, 0x02, 'a', 'c',
       0xa0, 0x03, 0x02, 0x01, 0x06, 0x81, 0x01, 0x04));
  INVALID(defL, defL(SOME_INT(0), NONE_SL, NONE_SL, NONE_INT, NONE_INT));   /* a = default */
  INVALID(defL, defL(NONE_INT, SOME_SL(SL(abcd)), NONE_SL, NONE_INT, NONE_INT)); /* b = default */
  INVALID(defL, defL(NONE_INT, NONE_SL, SOME_SL(SL(ab)), NONE_INT, NONE_INT)); /* s = default */
  INVALID(defL, defL(NONE_INT, NONE_SL, NONE_SL, SOME_INT(5), NONE_INT));   /* t = default */
  INVALID(defL, defL(NONE_INT, NONE_SL, NONE_SL, NONE_INT, SOME_INT(3)));   /* r = default */
  INVALID(defL, defL(NONE_INT, NONE_SL, NONE_SL, NONE_INT, SOME_INT(11)));  /* r > 10 */
  INVALID(defL, defL(NONE_INT, NONE_SL, NONE_SL, NONE_INT, SOME_INT(-1)));  /* r < 0 */

  /* tagS: restriction, implicitly tagged IA5String, 1-byte INTEGER */
  OK(tagS, tagS(SL(hi), 10, -128), V(0x30, 0x0a, 0x80, 0x02, 'h', 'i', 0x02, 0x01, 0x0a, 0x02, 0x01, 0x80));
  INVALID(tagS, tagS(SL(hi), 11, 0));     /* r > 10 */
  INVALID(tagS, tagS(SL(hi80), 0, 0));    /* not IA5 */
  INVALID(tagS, tagS(SL(hi), 0, 200));    /* s out of 1-byte bound */
  INVALID(tagS, tagS(SL(hi), 0, -129));

  /* neSeqOfInt: SIZE (1..MAX) */
  {
    ASN1_Pulse_Rel_asn1_int_impl xs[] = { SMALL(5), SMALL(-1) };
    OK(neSeqOfInt, ints(xs, 2), V(0x30, 0x06, 0x02, 0x01, 0x05, 0x02, 0x01, 0xff));
    INVALID(neSeqOfInt, ints(xs, 0));
  }

  /* setOfOctets: DER order of the elements */
  {
    Pulse_Lib_Slice_slice__uint8 sorted[] = { SL(aa), SL(aa00) };
    Pulse_Lib_Slice_slice__uint8 unsorted[] = { SL(aa00), SL(aa) };
    OK(setOfOctets, octs(sorted, 2), V(0x31, 0x07, 0x04, 0x01, 0xaa, 0x04, 0x02, 0xaa, 0x00));
    OK(setOfOctets, octs(sorted, 0), V(0x31, 0x00));
    INVALID(setOfOctets, octs(unsorted, 2));
  }

  /* setBAC: DEFAULT in a SET */
  OK(setBAC, setBAC(SOME_INT(-1), SOME_INT(7), SL(abcd)),
     V(0x31, 0x0a, 0x02, 0x01, 0xff, 0x80, 0x01, 0x07, 0x81, 0x02, 0xab, 0xcd));
  OK(setBAC, setBAC(NONE_INT, NONE_INT, SL(abcd)), V(0x31, 0x04, 0x81, 0x02, 0xab, 0xcd));
  INVALID(setBAC, setBAC(SOME_INT(0), NONE_INT, SL(abcd)));  /* b = default */

  printf(fails ? "FAIL\n" : "OK\n");
  return fails;
}
