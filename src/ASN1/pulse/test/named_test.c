/* Test of named C types through impl descriptors (ASN1.Pulse.NamedTest):

     Ch  ::= CHOICE { i INTEGER (small), o OCTET STRING }
     Rec ::= SEQUENCE { a INTEGER (small), b BOOLEAN OPTIONAL, c Ch }

   Write `Rec` structs with the JIT writers (`jit_rec`, `jit_raw_rec`,
   `jit_typed_rec`), check the DER bytes and JIT_NO_SPACE on a buffer one
   byte too short, then validate and parse the bytes back into a `Rec`
   (zero-copy), and parse then write them back (`roundtrip_rec`).

   KEEP-BYTES: `Outer ::= SEQUENCE { x INTEGER (small), r Rec }` with `r`
   keeping its bytes: the parser sets `r.kraw` to the bytes of `r` in the
   input, the writer ignores `kraw` (so a value built with no bytes can be
   written), and `roundtrip_outer` parses then writes back. */
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

static void roundtrip_ok(const char *name, uint8_t *in, size_t len) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 i = { .elt = in, .len = len };
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  if (ASN1_Pulse_NamedTest_roundtrip_rec(i, o, &pos) != ASN1_PULSE_JITWRITER_JIT_OK
      || pos != BUF - len || memcmp(out + pos, in, len) != 0) {
    printf("%s: roundtrip failed\n", name); fails++;
  }
}

static void write_outer_ok(const char *name, Outer x, const uint8_t *exp, size_t len) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  if (ASN1_Pulse_NamedTest_jit_typed_outer(x, o, &pos) != ASN1_PULSE_JITWRITER_JIT_OK
      || pos != BUF - len || memcmp(out + pos, exp, len) != 0) {
    printf("%s: write failed\n", name); fails++;
  }
}

int main(void) {
  /* { a 5, c i:7 } */
  Rec r1 = { .a = 5, .b = { .tag = ASN1_PULSE_NAMEDTEST_REC_B_ABSENT },
             .c = { .tag = ASN1_PULSE_NAMEDTEST_CH_I, .val = { .Ch_i = 7 } } };
  uint8_t e1[] = { 0x30, 0x06, 0x02, 0x01, 0x05, 0x02, 0x01, 0x07 };
  write_ok("jit r1", ASN1_Pulse_NamedTest_jit_rec, r1, e1, sizeof(e1));
  write_ok("jit_raw r1", ASN1_Pulse_NamedTest_jit_raw_rec, r1, e1, sizeof(e1));
  write_ok("jit_typed r1", ASN1_Pulse_NamedTest_jit_typed_rec, r1, e1, sizeof(e1));
  Rec p1 = parse_ok("r1", e1, sizeof(e1));
  if (p1.a != 5 || p1.b.tag != ASN1_PULSE_NAMEDTEST_REC_B_ABSENT
      || p1.c.tag != ASN1_PULSE_NAMEDTEST_CH_I || p1.c.val.Ch_i != 7) {
    printf("parse r1\n"); fails++;
  }
  roundtrip_ok("r1", e1, sizeof(e1));

  /* { a -129, b TRUE, c o:'0102'H } */
  uint8_t data[] = { 1, 2 };
  Rec r2 = { .a = -129,
             .b = { .tag = ASN1_PULSE_NAMEDTEST_REC_B_PRESENT, .val = { .Rec_b_present = true } },
             .c = { .tag = ASN1_PULSE_NAMEDTEST_CH_O,
                    .val = { .Ch_o = { .elt = data, .len = sizeof(data) } } } };
  uint8_t e2[] = { 0x30, 0x0b, 0x02, 0x02, 0xff, 0x7f, 0x01, 0x01, 0xff, 0x04, 0x02, 0x01, 0x02 };
  write_ok("jit r2", ASN1_Pulse_NamedTest_jit_rec, r2, e2, sizeof(e2));
  write_ok("jit_raw r2", ASN1_Pulse_NamedTest_jit_raw_rec, r2, e2, sizeof(e2));
  write_ok("jit_typed r2", ASN1_Pulse_NamedTest_jit_typed_rec, r2, e2, sizeof(e2));
  Rec p2 = parse_ok("r2", e2, sizeof(e2));
  if (p2.a != -129 || p2.b.tag != ASN1_PULSE_NAMEDTEST_REC_B_PRESENT || !p2.b.val.Rec_b_present
      || p2.c.tag != ASN1_PULSE_NAMEDTEST_CH_O || p2.c.val.Ch_o.len != 2 || p2.c.val.Ch_o.elt != e2 + 11) {
    printf("parse r2\n"); fails++;
  }
  roundtrip_ok("r2", e2, sizeof(e2));

  /* Not DER: BOOLEAN TRUE encoded as 0x01 */
  uint8_t bad[] = { 0x30, 0x0b, 0x02, 0x02, 0xff, 0x7f, 0x01, 0x01, 0x01, 0x04, 0x02, 0x01, 0x02 };
  size_t off = 0;
  Pulse_Lib_Slice_slice__uint8 sb = { .elt = bad, .len = sizeof(bad) };
  if (ASN1_Pulse_NamedTest_validate_rec(sb, &off)) { printf("bad accepted\n"); fails++; }

  /* KEEP-BYTES: { x 3, r r2 } */
  Outer o3 = { .x = 3, .r = { .kval = r2, .kraw = { .tag = FSTAR_PERVASIVES_NATIVE_NONE__SLICE_UINT8 } } };
  uint8_t e3[] = { 0x30, 0x10, 0x02, 0x01, 0x03,
                   0x30, 0x0b, 0x02, 0x02, 0xff, 0x7f, 0x01, 0x01, 0xff, 0x04, 0x02, 0x01, 0x02 };
  write_outer_ok("jit_typed o3 (no bytes)", o3, e3, sizeof(e3));
  {
    Pulse_Lib_Slice_slice__uint8 s3 = { .elt = e3, .len = sizeof(e3) };
    size_t off3 = 0;
    if (!ASN1_Pulse_NamedTest_validate_outer(s3, &off3) || off3 != sizeof(e3)) {
      printf("o3: validation failed\n"); fails++;
    }
    Outer p3 = ASN1_Pulse_NamedTest_parse_outer(s3);
    if (p3.x != 3 || p3.r.kraw.tag != FSTAR_PERVASIVES_NATIVE_SOME__SLICE_UINT8
        || p3.r.kraw.val.Some.elt != e3 + 5 || p3.r.kraw.val.Some.len != sizeof(e2)
        || p3.r.kval.a != -129 || p3.r.kval.c.tag != ASN1_PULSE_NAMEDTEST_CH_O
        || p3.r.kval.c.val.Ch_o.elt != e3 + 16) {
      printf("parse o3\n"); fails++;
    }
    write_outer_ok("jit_typed o3 (parsed, with bytes)", p3, e3, sizeof(e3));
  }
  {
    uint8_t out[BUF];
    size_t pos = BUF;
    Pulse_Lib_Slice_slice__uint8 i = { .elt = e3, .len = sizeof(e3) };
    Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
    if (ASN1_Pulse_NamedTest_roundtrip_outer(i, o, &pos) != ASN1_PULSE_JITWRITER_JIT_OK
        || pos != BUF - sizeof(e3) || memcmp(out + pos, e3, sizeof(e3)) != 0) {
      printf("o3: roundtrip failed\n"); fails++;
    }
  }

  if (fails) { printf("%d failure(s)\n", fails); return 1; }
  printf("named test: OK\n");
  return 0;
}
