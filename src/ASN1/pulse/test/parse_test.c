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
  printf(fails ? "FAIL\n" : "OK\n");
  return fails;
}
