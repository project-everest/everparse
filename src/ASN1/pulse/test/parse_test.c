/* Sanity test of the extracted zero-copy parsers (ASN1.Pulse.ParseTest) */
#include "ASN1.Pulse.ParseTest.h"
#include <stdio.h>
#define SL(a) ((Pulse_Lib_Slice_slice__uint8){ .elt = (a), .len = sizeof(a) })
int main(void) {
  int fails = 0;
  uint8_t i1[] = {0x02, 0x02, 0xff, 0x7f}; /* -129 */
  int64_t r = ASN1_Pulse_ParseTest_parse_int64(SL(i1));
  if (r != -129) { printf("int64 %lld\n", (long long)r); fails++; }
  uint8_t i2[] = {0x02, 0x08, 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff};
  if (ASN1_Pulse_ParseTest_parse_int64(SL(i2)) != INT64_MAX) { printf("max\n"); fails++; }
  uint8_t i3[] = {0x02, 0x01, 0x05};
  ASN1_Pulse_Rel_asn1_int_impl a = ASN1_Pulse_ParseTest_parse_int_(SL(i3));
  if (a.tag != ASN1_PULSE_REL_SMALL || a.val.Small != 5) { printf("int_\n"); fails++; }
  uint8_t i4[] = {0x02, 0x09, 0x00, 0x80,0,0,0,0,0,0,0};
  a = ASN1_Pulse_ParseTest_parse_int_(SL(i4));
  if (a.tag != ASN1_PULSE_REL_BIG || a.val.Big.len != 9 || a.val.Big.elt != i4 + 2) { printf("big\n"); fails++; }
  uint8_t b1[] = {0x01, 0x01, 0xff};
  if (!ASN1_Pulse_ParseTest_parse_bool_(SL(b1))) { printf("bool\n"); fails++; }
  uint8_t o1[] = {0x04, 0x03, 1, 2, 3};
  Pulse_Lib_Slice_slice__uint8 o = ASN1_Pulse_ParseTest_parse_octets(SL(o1));
  if (o.len != 3 || o.elt != o1 + 2) { printf("octets\n"); fails++; }
  uint8_t s1[] = {0x03, 0x03, 0x06, 0x6e, 0x40};
  ASN1_Pulse_Rel_asn1_bitstring_impl bs = ASN1_Pulse_ParseTest_parse_bits(SL(s1));
  if (bs.unused != 6 || bs.bytes.len != 2 || bs.bytes.elt != s1 + 3) { printf("bits\n"); fails++; }
  /* CHOICE { i INTEGER, b BOOLEAN, o [0] IMPLICIT OCTET STRING } */
  uint8_t c1[] = {0x02, 0x01, 0x07};
  FStar_Pervasives_either__asn1_int_impl_either_bool_slice_uint8 ch = ASN1_Pulse_ParseTest_parse_choice_(SL(c1));
  if (ch.tag != FSTAR_PERVASIVES_INL__ASN1_INT_IMPL_EITHER_BOOL_SLICE_UINT8 || ch.val.Inl.tag != ASN1_PULSE_REL_SMALL || ch.val.Inl.val.Small != 7) { printf("choice i\n"); fails++; }
  uint8_t c2[] = {0x01, 0x01, 0x00};
  ch = ASN1_Pulse_ParseTest_parse_choice_(SL(c2));
  if (ch.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_EITHER_BOOL_SLICE_UINT8 || ch.val.Inr.tag != FSTAR_PERVASIVES_INL__BOOL_SLICE_UINT8 || ch.val.Inr.val.Inl) { printf("choice b\n"); fails++; }
  uint8_t c3[] = {0x80, 0x02, 9, 8};
  ch = ASN1_Pulse_ParseTest_parse_choice_(SL(c3));
  if (ch.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_EITHER_BOOL_SLICE_UINT8 || ch.val.Inr.tag != FSTAR_PERVASIVES_INR__BOOL_SLICE_UINT8 || ch.val.Inr.val.Inr.len != 2 || ch.val.Inr.val.Inr.elt != c3 + 2) { printf("choice o\n"); fails++; }
  /* SEQUENCE { a INTEGER } and SEQUENCE { a INTEGER, b BOOLEAN } */
  uint8_t q1[] = {0x30, 0x03, 0x02, 0x01, 0x05};
  a = ASN1_Pulse_ParseTest_parse_seqA(SL(q1));
  if (a.tag != ASN1_PULSE_REL_SMALL || a.val.Small != 5) { printf("seqA\n"); fails++; }
  uint8_t q2[] = {0x30, 0x06, 0x02, 0x01, 0x05, 0x01, 0x01, 0xff};
  FStar_Pervasives_Native_tuple2__asn1_int_impl_bool ab = ASN1_Pulse_ParseTest_parse_seqAB(SL(q2));
  if (ab._1.tag != ASN1_PULSE_REL_SMALL || ab._1.val.Small != 5 || !ab._2) { printf("seqAB\n"); fails++; }
  /* SEQUENCE { a INTEGER, b BOOLEAN DEFAULT FALSE,
       c [0] IMPLICIT OCTET STRING OPTIONAL, d [1] EXPLICIT INTEGER OPTIONAL } */
  uint8_t q3[] = {0x30, 0x03, 0x02, 0x01, 0x05};
  FStar_Pervasives_Native_tuple2__asn1_int_impl_tuple2_option_bool_tuple2_option_s q =
    ASN1_Pulse_ParseTest_parse_seq(SL(q3));
  if (q._1.val.Small != 5 || q._2._1.tag != FSTAR_PERVASIVES_NATIVE_NONE__BOOL
      || q._2._2._1.tag != FSTAR_PERVASIVES_NATIVE_NONE__SLICE_UINT8
      || q._2._2._2.tag != FSTAR_PERVASIVES_NATIVE_NONE__ASN1_INT_IMPL) { printf("seq a\n"); fails++; }
  uint8_t q4[] = {0x30, 0x0f, 0x02, 0x01, 0x05, 0x01, 0x01, 0xff, 0x80, 0x02, 0xaa, 0xbb, 0xa1, 0x03, 0x02, 0x01, 0x07};
  q = ASN1_Pulse_ParseTest_parse_seq(SL(q4));
  if (q._1.val.Small != 5 || q._2._1.tag != FSTAR_PERVASIVES_NATIVE_SOME__BOOL || !q._2._1.val.Some
      || q._2._2._1.tag != FSTAR_PERVASIVES_NATIVE_SOME__SLICE_UINT8 || q._2._2._1.val.Some.len != 2 || q._2._2._1.val.Some.elt != q4 + 10
      || q._2._2._2.tag != FSTAR_PERVASIVES_NATIVE_SOME__ASN1_INT_IMPL || q._2._2._2.val.Some.val.Small != 7) { printf("seq abcd\n"); fails++; }
  uint8_t q5[] = {0x30, 0x08, 0x02, 0x01, 0x05, 0xa1, 0x03, 0x02, 0x01, 0x07};
  q = ASN1_Pulse_ParseTest_parse_seq(SL(q5));
  if (q._1.val.Small != 5 || q._2._1.tag != FSTAR_PERVASIVES_NATIVE_NONE__BOOL
      || q._2._2._1.tag != FSTAR_PERVASIVES_NATIVE_NONE__SLICE_UINT8
      || q._2._2._2.tag != FSTAR_PERVASIVES_NATIVE_SOME__ASN1_INT_IMPL || q._2._2._2.val.Some.val.Small != 7) { printf("seq ad\n"); fails++; }
  /* SEQUENCE OF INTEGER and SET OF OCTET STRING: lazy, count + payload */
  uint8_t l1[] = {0x30, 0x09, 0x02, 0x01, 0x05, 0x02, 0x01, 0x06, 0x02, 0x01, 0x07};
  LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_asn1_int_impl li = ASN1_Pulse_ParseTest_parse_seqOfInt(SL(l1));
  if (li.tag != LOWPARSE_PULSEPARSE_ITERATOR_TYPE_BASE__UINTSIZE_ASN1_INT_IMPL
      || li.val.Base.tag != LOWPARSE_PULSEPARSE_ITERATOR_TYPE_SERIALIZED__UINTSIZE_ASN1_INT_IMPL
      || li.val.Base.val.Serialized.count != 3 || li.val.Base.val.Serialized.payload.elt != l1 + 2
      || li.val.Base.val.Serialized.payload.len != 9) { printf("seqOfInt\n"); fails++; }
  uint8_t l2[] = {0x30, 0x00};
  li = ASN1_Pulse_ParseTest_parse_seqOfInt(SL(l2));
  if (li.val.Base.val.Serialized.count != 0 || li.val.Base.val.Serialized.payload.len != 0) { printf("seqOfInt empty\n"); fails++; }
  uint8_t l3[] = {0x31, 0x07, 0x04, 0x01, 0xaa, 0x04, 0x02, 0xaa, 0x00};
  LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 lo = ASN1_Pulse_ParseTest_parse_setOfOctets(SL(l3));
  if (lo.tag != LOWPARSE_PULSEPARSE_ITERATOR_TYPE_BASE__UINTSIZE_SLICE_UINT8
      || lo.val.Base.tag != LOWPARSE_PULSEPARSE_ITERATOR_TYPE_SERIALIZED__UINTSIZE_SLICE_UINT8
      || lo.val.Base.val.Serialized.count != 2 || lo.val.Base.val.Serialized.payload.elt != l3 + 2
      || lo.val.Base.val.Serialized.payload.len != 7) { printf("setOfOctets\n"); fails++; }
  /* SET { b BOOLEAN, a [0] IMPLICIT INTEGER OPTIONAL, c [1] IMPLICIT OCTET STRING } */
  uint8_t t1[] = {0x31, 0x0a, 0x01, 0x01, 0xff, 0x80, 0x01, 0x07, 0x81, 0x02, 0xaa, 0xbb};
  FStar_Pervasives_Native_tuple2__bool_tuple2_option_asn1_int_impl_slice_uint8 st = ASN1_Pulse_ParseTest_parse_setBAC(SL(t1));
  if (!st._1 || st._2._1.tag != FSTAR_PERVASIVES_NATIVE_SOME__ASN1_INT_IMPL || st._2._1.val.Some.val.Small != 7
      || st._2._2.len != 2 || st._2._2.elt != t1 + 10) { printf("setBAC\n"); fails++; }
  uint8_t t2[] = {0x31, 0x07, 0x01, 0x01, 0x00, 0x81, 0x02, 0xaa, 0xbb};
  st = ASN1_Pulse_ParseTest_parse_setBAC(SL(t2));
  if (st._1 || st._2._1.tag != FSTAR_PERVASIVES_NATIVE_NONE__ASN1_INT_IMPL
      || st._2._2.len != 2 || st._2._2.elt != t2 + 7) { printf("setBC\n"); fails++; }
  printf(fails ? "FAIL\n" : "OK\n");
  return fails;
}
