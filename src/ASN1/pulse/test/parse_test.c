/* Sanity test of the extracted zero-copy parsers (ASN1.Pulse.ParseTest) */
#include "ASN1.Pulse.ParseTest.h"
#include <stdio.h>
#define SL(a) ((Pulse_Lib_Slice_slice__uint8){ .elt = (a), .len = sizeof(a) })
static int valid(bool (*f)(Pulse_Lib_Slice_slice__uint8, size_t *), Pulse_Lib_Slice_slice__uint8 s) {
  size_t off = 0;
  return f(s, &off) && off == s.len;
}
#define VALID(f, a) valid(f, SL(a))
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
  /* ANY DEFINED BY (OBJECT IDENTIFIER keys): 1.2.3 -> NULL, 1.2.4 -> INTEGER */
  uint8_t a1[] = {0x30, 0x09, 0x02, 0x01, 0x05, 0x06, 0x02, 0x2a, 0x03, 0x05, 0x00};
  FStar_Pervasives_Native_tuple2__asn1_int_impl_either_unit_asn1_int_impl ap = ASN1_Pulse_ParseTest_parse_adbP(SL(a1));
  if (ap._1.val.Small != 5 || ap._2.tag != FSTAR_PERVASIVES_INL__UNIT_ASN1_INT_IMPL) { printf("adbP 1.2.3\n"); fails++; }
  uint8_t a2[] = {0x30, 0x0a, 0x02, 0x01, 0x05, 0x06, 0x02, 0x2a, 0x04, 0x02, 0x01, 0x07};
  ap = ASN1_Pulse_ParseTest_parse_adbP(SL(a2));
  if (ap._1.val.Small != 5 || ap._2.tag != FSTAR_PERVASIVES_INR__UNIT_ASN1_INT_IMPL || ap._2.val.Inr.val.Small != 7) { printf("adbP 1.2.4\n"); fails++; }
  /* ... with a fallback: an unknown OID followed by an OPTIONAL ANY */
  uint8_t f1[] = {0x30, 0x06, 0x06, 0x02, 0x2a, 0x03, 0x05, 0x00};
  FStar_Pervasives_either__unit_either_asn1_int_impl_tuple2_slice_uint8_opt af = ASN1_Pulse_ParseTest_parse_adbF(SL(f1));
  if (af.tag != FSTAR_PERVASIVES_INL__UNIT_EITHER_ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPT) { printf("adbF 1.2.3\n"); fails++; }
  uint8_t f2[] = {0x30, 0x07, 0x06, 0x02, 0x2a, 0x04, 0x02, 0x01, 0x07};
  af = ASN1_Pulse_ParseTest_parse_adbF(SL(f2));
  if (af.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPT
      || af.val.Inr.tag != FSTAR_PERVASIVES_INL__ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPTION_SLICE_UI
      || af.val.Inr.val.Inl.val.Small != 7) { printf("adbF 1.2.4\n"); fails++; }
  uint8_t f3[] = {0x30, 0x04, 0x06, 0x02, 0x2a, 0x05};
  af = ASN1_Pulse_ParseTest_parse_adbF(SL(f3));
  if (af.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPT
      || af.val.Inr.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPTION_SLICE_UI
      || af.val.Inr.val.Inr._1.len != 2 || af.val.Inr.val.Inr._1.elt != f3 + 4
      || af.val.Inr.val.Inr._2.tag != FSTAR_PERVASIVES_NATIVE_NONE__SLICE_UINT8) { printf("adbF 1.2.5\n"); fails++; }
  uint8_t f4[] = {0x30, 0x07, 0x06, 0x02, 0x2a, 0x05, 0x01, 0x01, 0xff};
  af = ASN1_Pulse_ParseTest_parse_adbF(SL(f4));
  if (af.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPT
      || af.val.Inr.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPTION_SLICE_UI
      || af.val.Inr.val.Inr._1.len != 2 || af.val.Inr.val.Inr._1.elt != f4 + 4
      || af.val.Inr.val.Inr._2.tag != FSTAR_PERVASIVES_NATIVE_SOME__SLICE_UINT8
      || af.val.Inr.val.Inr._2.val.Some.len != 3 || af.val.Inr.val.Inr._2.val.Some.elt != f4 + 6) { printf("adbF 1.2.5 any\n"); fails++; }
  /* ANY DEFINED BY with non-OID keys, compared byte-for-byte */
  /* OCTET STRING keys: 'AA'H -> NULL, 'AABB'H -> INTEGER, fallback OPTIONAL ANY */
  uint8_t ko1[] = {0x30, 0x05, 0x04, 0x01, 0xaa, 0x05, 0x00};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbO, ko1)) { printf("adbO valid AA\n"); fails++; }
  af = ASN1_Pulse_ParseTest_parse_adbO(SL(ko1));
  if (af.tag != FSTAR_PERVASIVES_INL__UNIT_EITHER_ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPT) { printf("adbO AA\n"); fails++; }
  uint8_t ko2[] = {0x30, 0x07, 0x04, 0x02, 0xaa, 0xbb, 0x02, 0x01, 0x07};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbO, ko2)) { printf("adbO valid AABB\n"); fails++; }
  af = ASN1_Pulse_ParseTest_parse_adbO(SL(ko2));
  if (af.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPT
      || af.val.Inr.tag != FSTAR_PERVASIVES_INL__ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPTION_SLICE_UI
      || af.val.Inr.val.Inl.val.Small != 7) { printf("adbO AABB\n"); fails++; }
  uint8_t ko3[] = {0x30, 0x04, 0x04, 0x02, 0xaa, 0x00}; /* 'AA00'H: a strict extension of 'AA'H, so the fallback */
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbO, ko3)) { printf("adbO valid AA00\n"); fails++; }
  af = ASN1_Pulse_ParseTest_parse_adbO(SL(ko3));
  if (af.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPT
      || af.val.Inr.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPTION_SLICE_UI
      || af.val.Inr.val.Inr._1.len != 2 || af.val.Inr.val.Inr._1.elt != ko3 + 4
      || af.val.Inr.val.Inr._2.tag != FSTAR_PERVASIVES_NATIVE_NONE__SLICE_UINT8) { printf("adbO AA00\n"); fails++; }
  uint8_t ko4[] = {0x30, 0x06, 0x04, 0x01, 0xbb, 0x01, 0x01, 0xff};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbO, ko4)) { printf("adbO valid BB\n"); fails++; }
  af = ASN1_Pulse_ParseTest_parse_adbO(SL(ko4));
  if (af.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPT
      || af.val.Inr.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_TUPLE2_SLICE_UINT8_OPTION_SLICE_UI
      || af.val.Inr.val.Inr._1.len != 1 || af.val.Inr.val.Inr._1.elt != ko4 + 4
      || af.val.Inr.val.Inr._2.tag != FSTAR_PERVASIVES_NATIVE_SOME__SLICE_UINT8
      || af.val.Inr.val.Inr._2.val.Some.len != 3 || af.val.Inr.val.Inr._2.val.Some.elt != ko4 + 5) { printf("adbO BB\n"); fails++; }
  uint8_t ko5[] = {0x30, 0x06, 0x04, 0x02, 0xaa, 0xbb, 0x05, 0x00}; /* 'AABB'H requires an INTEGER */
  if (VALID(ASN1_Pulse_ParseTest_validate_adbO, ko5)) { printf("adbO invalid AABB NULL\n"); fails++; }
  uint8_t ko6[] = {0x30, 0x03, 0x04, 0x01, 0xaa}; /* 'AA'H requires a NULL */
  if (VALID(ASN1_Pulse_ParseTest_validate_adbO, ko6)) { printf("adbO invalid AA\n"); fails++; }
  /* BOOLEAN keys after an INTEGER prefix: TRUE -> INTEGER, FALSE -> NULL */
  uint8_t kb1[] = {0x30, 0x09, 0x02, 0x01, 0x05, 0x01, 0x01, 0xff, 0x02, 0x01, 0x07};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbB, kb1)) { printf("adbB valid TRUE\n"); fails++; }
  FStar_Pervasives_Native_tuple2__asn1_int_impl_either_asn1_int_impl_unit akb = ASN1_Pulse_ParseTest_parse_adbB(SL(kb1));
  if (akb._1.val.Small != 5 || akb._2.tag != FSTAR_PERVASIVES_INL__ASN1_INT_IMPL_UNIT || akb._2.val.Inl.val.Small != 7) { printf("adbB TRUE\n"); fails++; }
  uint8_t kb2[] = {0x30, 0x08, 0x02, 0x01, 0x05, 0x01, 0x01, 0x00, 0x05, 0x00};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbB, kb2)) { printf("adbB valid FALSE\n"); fails++; }
  akb = ASN1_Pulse_ParseTest_parse_adbB(SL(kb2));
  if (akb._1.val.Small != 5 || akb._2.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_UNIT) { printf("adbB FALSE\n"); fails++; }
  uint8_t kb3[] = {0x30, 0x08, 0x02, 0x01, 0x05, 0x01, 0x01, 0xff, 0x05, 0x00};
  if (VALID(ASN1_Pulse_ParseTest_validate_adbB, kb3)) { printf("adbB invalid TRUE NULL\n"); fails++; }
  uint8_t kb4[] = {0x30, 0x08, 0x02, 0x01, 0x05, 0x01, 0x01, 0x01, 0x05, 0x00}; /* not DER */
  if (VALID(ASN1_Pulse_ParseTest_validate_adbB, kb4)) { printf("adbB invalid BER TRUE\n"); fails++; }
  /* PrintableString keys: "akb" -> INTEGER, "a" -> NULL, no fallback */
  uint8_t kp1[] = {0x30, 0x07, 0x13, 0x02, 0x61, 0x62, 0x02, 0x01, 0x07};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbS, kp1)) { printf("adbS valid akb\n"); fails++; }
  FStar_Pervasives_either__asn1_int_impl_unit aks = ASN1_Pulse_ParseTest_parse_adbS(SL(kp1));
  if (aks.tag != FSTAR_PERVASIVES_INL__ASN1_INT_IMPL_UNIT || aks.val.Inl.val.Small != 7) { printf("adbS akb\n"); fails++; }
  uint8_t kp2[] = {0x30, 0x05, 0x13, 0x01, 0x61, 0x05, 0x00};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbS, kp2)) { printf("adbS valid a\n"); fails++; }
  aks = ASN1_Pulse_ParseTest_parse_adbS(SL(kp2));
  if (aks.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_UNIT) { printf("adbS a\n"); fails++; }
  uint8_t kp3[] = {0x30, 0x05, 0x13, 0x01, 0x62, 0x05, 0x00}; /* unknown key, no fallback */
  if (VALID(ASN1_Pulse_ParseTest_validate_adbS, kp3)) { printf("adbS invalid b\n"); fails++; }
  uint8_t kp4[] = {0x30, 0x06, 0x13, 0x02, 0x61, 0x62, 0x05, 0x00};
  if (VALID(ASN1_Pulse_ParseTest_validate_adbS, kp4)) { printf("adbS invalid akb NULL\n"); fails++; }
  /* ANY DEFINED BY an INTEGER key */
  uint8_t ki1[] = {0x30, 0x05, 0x02, 0x01, 0x01, 0x05, 0x00};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbI, ki1)) { printf("adbI valid 1\n"); fails++; }
  FStar_Pervasives_either__unit_either_asn1_int_impl_either_unit_tuple2_asn aki = ASN1_Pulse_ParseTest_parse_adbI(SL(ki1));
  if (aki.tag != FSTAR_PERVASIVES_INL__UNIT_EITHER_ASN1_INT_IMPL_EITHER_UNIT_TUPLE2_ASN) { printf("adbI 1\n"); fails++; }
  uint8_t ki2[] = {0x30, 0x06, 0x02, 0x01, 0xff, 0x02, 0x01, 0x07};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbI, ki2)) { printf("adbI valid -1\n"); fails++; }
  aki = ASN1_Pulse_ParseTest_parse_adbI(SL(ki2));
  if (aki.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_EITHER_UNIT_TUPLE2_ASN
      || aki.val.Inr.tag != FSTAR_PERVASIVES_INL__ASN1_INT_IMPL_EITHER_UNIT_TUPLE2_ASN1_INT_IMPL_O
      || aki.val.Inr.val.Inl.val.Small != 7) { printf("adbI -1\n"); fails++; }
  uint8_t ki3[] = {0x30, 0x0d, 0x02, 0x09, 0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0x05, 0x00};
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbI, ki3)) { printf("adbI valid 2^64\n"); fails++; }
  aki = ASN1_Pulse_ParseTest_parse_adbI(SL(ki3));
  if (aki.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_EITHER_UNIT_TUPLE2_ASN
      || aki.val.Inr.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_EITHER_UNIT_TUPLE2_ASN1_INT_IMPL_O
      || aki.val.Inr.val.Inr.tag != FSTAR_PERVASIVES_INL__UNIT_TUPLE2_ASN1_INT_IMPL_OPTION_SLICE_UINT8) { printf("adbI 2^64\n"); fails++; }
  uint8_t ki4[] = {0x30, 0x03, 0x02, 0x01, 0x02}; /* unknown key, fallback, absent */
  if (!VALID(ASN1_Pulse_ParseTest_validate_adbI, ki4)) { printf("adbI valid 2\n"); fails++; }
  aki = ASN1_Pulse_ParseTest_parse_adbI(SL(ki4));
  if (aki.tag != FSTAR_PERVASIVES_INR__UNIT_EITHER_ASN1_INT_IMPL_EITHER_UNIT_TUPLE2_ASN
      || aki.val.Inr.tag != FSTAR_PERVASIVES_INR__ASN1_INT_IMPL_EITHER_UNIT_TUPLE2_ASN1_INT_IMPL_O
      || aki.val.Inr.val.Inr.tag != FSTAR_PERVASIVES_INR__UNIT_TUPLE2_ASN1_INT_IMPL_OPTION_SLICE_UINT8
      || aki.val.Inr.val.Inr.val.Inr._1.val.Small != 2
      || aki.val.Inr.val.Inr.val.Inr._2.tag != FSTAR_PERVASIVES_NATIVE_NONE__SLICE_UINT8) { printf("adbI 2\n"); fails++; }
  uint8_t ki5[] = {0x30, 0x0e, 0x02, 0x09, 0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0x02, 0x01, 0x07}; /* 2^64 -> NULL, not INTEGER */
  if (VALID(ASN1_Pulse_ParseTest_validate_adbI, ki5)) { printf("adbI invalid 2^64 INTEGER\n"); fails++; }
  uint8_t ki6[] = {0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x07}; /* 1 -> NULL, not INTEGER */
  if (VALID(ASN1_Pulse_ParseTest_validate_adbI, ki6)) { printf("adbI invalid 1 INTEGER\n"); fails++; }
  uint8_t ki7[] = {0x30, 0x06, 0x02, 0x02, 0x00, 0x01, 0x05, 0x00}; /* non-minimal key */
  if (VALID(ASN1_Pulse_ParseTest_validate_adbI, ki7)) { printf("adbI invalid non-minimal\n"); fails++; }
  /* AlgorithmIdentifier from the difftest schemas */
  uint8_t g1[] = {0x30, 0x06, 0x06, 0x02, 0x2a, 0x03, 0x05, 0x00};
  FStar_Pervasives_either__unit_tuple2_slice_uint8_option_slice_uint8 ag = ASN1_Pulse_ParseTest_parse_algId(SL(g1));
  if (ag.tag != FSTAR_PERVASIVES_INL__UNIT_TUPLE2_SLICE_UINT8_OPTION_SLICE_UINT8) { printf("algId 1.2.3\n"); fails++; }
  uint8_t g2[] = {0x30, 0x07, 0x06, 0x02, 0x2a, 0x07, 0x02, 0x01, 0x07};
  ag = ASN1_Pulse_ParseTest_parse_algId(SL(g2));
  if (ag.tag != FSTAR_PERVASIVES_INR__UNIT_TUPLE2_SLICE_UINT8_OPTION_SLICE_UINT8
      || ag.val.Inr._1.len != 2 || ag.val.Inr._1.elt != g2 + 4
      || ag.val.Inr._2.tag != FSTAR_PERVASIVES_NATIVE_SOME__SLICE_UINT8
      || ag.val.Inr._2.val.Some.len != 3 || ag.val.Inr._2.val.Some.elt != g2 + 6) { printf("algId other\n"); fails++; }
  printf(fails ? "FAIL\n" : "OK\n");
  return fails;
}
