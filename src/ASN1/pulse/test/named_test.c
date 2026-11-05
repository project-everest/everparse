/* Test of named C types through impl descriptors (ASN1.Pulse.NamedTest):

     Ch  ::= CHOICE { i INTEGER (small), o OCTET STRING }
     Rec ::= SEQUENCE { a INTEGER (small), b BOOLEAN OPTIONAL, c Ch }

   Write `Rec` structs with both JIT writers (`jit_rec`, `jit_raw_rec`),
   check the DER bytes and JIT_NO_SPACE on a buffer one byte too short,
   then validate and parse the bytes back into a `Rec` (zero-copy). */
#include "ASN1.Pulse.NamedTest.h"
#include <stdio.h>
#include <string.h>
#define BUF 64

static int fails = 0;

typedef ASN1_Pulse_JitWriter_jit_result (*writer)(Rec, Pulse_Lib_Slice_slice__uint8, size_t *);

static void write_ok(const char *name, writer w, Rec x, const uint8_t *exp, size_t len) {
  uint8_t out[BUF + 1];
  memset(out, 0xcc, sizeof(out));
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out + 1, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = w(x, o, &pos);
  if (r != ASN1_PULSE_JITWRITER_JIT_OK || pos != BUF - len || memcmp(out + 1 + pos, exp, len) != 0) {
    printf("%s: expected OK (%d)\n", name, (int)r); fails++;
  }
  for (size_t i = 0; i < 1 + pos && i <= BUF; i++)
    if (out[i] != 0xcc) { printf("%s: wrote left of pos\n", name); fails++; break; }
  memset(out, 0xcc, sizeof(out));
  pos = len - 1;
  Pulse_Lib_Slice_slice__uint8 s = { .elt = out + 1, .len = len - 1 };
  if (w(x, s, &pos) != ASN1_PULSE_JITWRITER_JIT_NO_SPACE || out[0] != 0xcc) {
    printf("%s: short buffer: expected NO_SPACE\n", name); fails++;
  }
}

static Rec parse_ok(const char *name, uint8_t *in, size_t len) {
  Pulse_Lib_Slice_slice__uint8 s = { .elt = in, .len = len };
  size_t off = 0;
  if (!ASN1_Pulse_NamedTest_validate_rec(s, &off) || off != len) {
    printf("%s: validation failed\n", name); fails++;
  }
  return ASN1_Pulse_NamedTest_parse_rec(s);
}

int main(void) {
  /* { a 5, c i:7 } */
  Rec r1 = { .a = 5, .b = { .tag = ASN1_PULSE_NAMEDTEST_REC_B_ABSENT },
             .c = { .tag = ASN1_PULSE_NAMEDTEST_CH_I, .val = { .Ch_i = 7 } } };
  uint8_t e1[] = { 0x30, 0x06, 0x02, 0x01, 0x05, 0x02, 0x01, 0x07 };
  write_ok("jit r1", ASN1_Pulse_NamedTest_jit_rec, r1, e1, sizeof(e1));
  write_ok("jit_raw r1", ASN1_Pulse_NamedTest_jit_raw_rec, r1, e1, sizeof(e1));
  Rec p1 = parse_ok("r1", e1, sizeof(e1));
  if (p1.a != 5 || p1.b.tag != ASN1_PULSE_NAMEDTEST_REC_B_ABSENT
      || p1.c.tag != ASN1_PULSE_NAMEDTEST_CH_I || p1.c.val.Ch_i != 7) {
    printf("parse r1\n"); fails++;
  }

  /* { a -129, b TRUE, c o:'0102'H } */
  uint8_t data[] = { 1, 2 };
  Rec r2 = { .a = -129,
             .b = { .tag = ASN1_PULSE_NAMEDTEST_REC_B_PRESENT, .val = { .Rec_b_present = true } },
             .c = { .tag = ASN1_PULSE_NAMEDTEST_CH_O,
                    .val = { .Ch_o = { .elt = data, .len = sizeof(data) } } } };
  uint8_t e2[] = { 0x30, 0x0b, 0x02, 0x02, 0xff, 0x7f, 0x01, 0x01, 0xff, 0x04, 0x02, 0x01, 0x02 };
  write_ok("jit r2", ASN1_Pulse_NamedTest_jit_rec, r2, e2, sizeof(e2));
  write_ok("jit_raw r2", ASN1_Pulse_NamedTest_jit_raw_rec, r2, e2, sizeof(e2));
  Rec p2 = parse_ok("r2", e2, sizeof(e2));
  if (p2.a != -129 || p2.b.tag != ASN1_PULSE_NAMEDTEST_REC_B_PRESENT || !p2.b.val.Rec_b_present
      || p2.c.tag != ASN1_PULSE_NAMEDTEST_CH_O || p2.c.val.Ch_o.len != 2 || p2.c.val.Ch_o.elt != e2 + 11) {
    printf("parse r2\n"); fails++;
  }

  /* Not DER: BOOLEAN TRUE encoded as 0x01 */
  uint8_t bad[] = { 0x30, 0x0b, 0x02, 0x02, 0xff, 0x7f, 0x01, 0x01, 0x01, 0x04, 0x02, 0x01, 0x02 };
  size_t off = 0;
  Pulse_Lib_Slice_slice__uint8 sb = { .elt = bad, .len = sizeof(bad) };
  if (ASN1_Pulse_NamedTest_validate_rec(sb, &off)) { printf("bad accepted\n"); fails++; }

  if (fails) { printf("%d failure(s)\n", fails); return 1; }
  printf("named test: OK\n");
  return 0;
}
