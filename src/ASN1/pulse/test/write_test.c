/* Round-trip test of the extracted right-to-left writers (ASN1.Pulse.ParseTest):
   parse a DER encoding, write the parsed value back from the right edge of an
   output buffer, and compare the bytes. Also check that the writers fail
   without writing past the left edge when the buffer is one byte too short. */
#include "ASN1.Pulse.ParseTest.h"
#include <stdio.h>
#include <string.h>
#define SL(a) ((Pulse_Lib_Slice_slice__uint8){ .elt = (a), .len = sizeof(a) })
#define BUF 64

static int fails = 0;

#define RT(name, vec) do {                                                   \
    uint8_t in_[] = vec;                                                      \
    __typeof__(ASN1_Pulse_ParseTest_parse_##name(SL(in_))) x_ =               \
      ASN1_Pulse_ParseTest_parse_##name(SL(in_));                             \
    uint8_t out_[BUF + 1];                                                    \
    memset(out_, 0xcc, sizeof(out_));                                         \
    size_t pos_ = BUF;                                                        \
    Pulse_Lib_Slice_slice__uint8 o_ = { .elt = out_ + 1, .len = BUF };        \
    bool ok_ = ASN1_Pulse_ParseTest_write_##name(x_, o_, &pos_);              \
    if (!ok_ || pos_ != BUF - sizeof(in_)                                     \
        || memcmp(out_ + 1 + pos_, in_, sizeof(in_)) != 0) {                  \
      printf("%s: round trip\n", #name); fails++;                             \
    }                                                                         \
    for (size_t i_ = 0; i_ < 1 + pos_ && i_ <= BUF; i_++)                     \
      if (out_[i_] != 0xcc) { printf("%s: wrote left of pos\n", #name); fails++; break; } \
    memset(out_, 0xcc, sizeof(out_));                                         \
    pos_ = sizeof(in_) - 1;                                                   \
    Pulse_Lib_Slice_slice__uint8 s_ = { .elt = out_ + 1, .len = sizeof(in_) - 1 }; \
    if (ASN1_Pulse_ParseTest_write_##name(x_, s_, &pos_) || out_[0] != 0xcc) { \
      printf("%s: short buffer\n", #name); fails++;                           \
    }                                                                         \
  } while (0)
#define V(...) { __VA_ARGS__ }

int main(void) {
  RT(int64, V(0x02, 0x02, 0xff, 0x7f));
  RT(int64, V(0x02, 0x08, 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff));
  RT(int64, V(0x02, 0x01, 0x00));
  RT(int_, V(0x02, 0x01, 0x05));
  RT(int_, V(0x02, 0x09, 0x00, 0x80,0,0,0,0,0,0,0));
  RT(bool_, V(0x01, 0x01, 0xff));
  RT(bool_, V(0x01, 0x01, 0x00));
  RT(octets, V(0x04, 0x03, 1, 2, 3));
  RT(octets, V(0x04, 0x00));
  RT(bits, V(0x03, 0x03, 0x06, 0x6e, 0x40));
  RT(choice_, V(0x02, 0x01, 0x07));
  RT(choice_, V(0x01, 0x01, 0x00));
  RT(choice_, V(0x80, 0x02, 9, 8));
  RT(seqA, V(0x30, 0x03, 0x02, 0x01, 0x05));
  RT(seqAB, V(0x30, 0x06, 0x02, 0x01, 0x05, 0x01, 0x01, 0xff));
  RT(seq, V(0x30, 0x03, 0x02, 0x01, 0x05));
  RT(seq, V(0x30, 0x0f, 0x02, 0x01, 0x05, 0x01, 0x01, 0xff, 0x80, 0x02, 0xaa, 0xbb, 0xa1, 0x03, 0x02, 0x01, 0x07));
  RT(seq, V(0x30, 0x08, 0x02, 0x01, 0x05, 0xa1, 0x03, 0x02, 0x01, 0x07));
  RT(seqOfInt, V(0x30, 0x09, 0x02, 0x01, 0x05, 0x02, 0x01, 0x06, 0x02, 0x01, 0x07));
  RT(seqOfInt, V(0x30, 0x00));
  RT(setOfOctets, V(0x31, 0x07, 0x04, 0x01, 0xaa, 0x04, 0x02, 0xaa, 0x00));
  RT(setBAC, V(0x31, 0x0a, 0x01, 0x01, 0xff, 0x80, 0x01, 0x07, 0x81, 0x02, 0xaa, 0xbb));
  RT(setBAC, V(0x31, 0x07, 0x01, 0x01, 0x00, 0x81, 0x02, 0xaa, 0xbb));
  /* Values built directly in C, not from a parse */
  {
    uint8_t out[BUF]; size_t pos = BUF;
    Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
    uint8_t exp1[] = {0x02, 0x02, 0x00, 0x80};
    if (!ASN1_Pulse_ParseTest_write_int64(128, o, &pos) || pos != BUF - 4 || memcmp(out + pos, exp1, 4)) { printf("int64 128\n"); fails++; }
    uint8_t exp2[] = {0x02, 0x08, 0x80, 0, 0, 0, 0, 0, 0, 0, 0x02, 0x02, 0x00, 0x80};
    if (!ASN1_Pulse_ParseTest_write_int64(INT64_MIN, o, &pos) || pos != BUF - 14 || memcmp(out + pos, exp2, 14)) { printf("int64 min, appended\n"); fails++; }
    FStar_Pervasives_Native_tuple2__asn1_int_impl_bool ab = { ._1 = { .tag = ASN1_PULSE_REL_SMALL, .val = { .Small = -1 } }, ._2 = false };
    pos = BUF;
    uint8_t exp3[] = {0x30, 0x06, 0x02, 0x01, 0xff, 0x01, 0x01, 0x00};
    if (!ASN1_Pulse_ParseTest_write_seqAB(ab, o, &pos) || pos != BUF - 8 || memcmp(out + pos, exp3, 8)) { printf("seqAB built\n"); fails++; }
  }
  printf(fails ? "FAIL\n" : "OK\n");
  return fails;
}
