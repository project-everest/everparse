/* Round trip through the C API that everparse-asn1 generates for Small.asn:
   write `Msg` values (right to left), check the DER bytes, JIT_NO_SPACE and
   JIT_INVALID, then validate and parse the bytes back; also check SIZE
   constraints on character strings (`Names`). */
#include "Small.h"
#include <stdio.h>
#include <string.h>
#define BUF 128

static int fails = 0;
#define CHECK(c, ...) do { if (!(c)) { printf(__VA_ARGS__); printf("\n"); fails++; } } while (0)

static Pulse_Lib_Slice_slice__uint8 sl(const char *s) {
  return (Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)s, .len = strlen(s) };
}

typedef LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 octs_t;

static octs_t octs(Pulse_Lib_Slice_slice__uint8 *a, size_t n) {
  octs_t l = { .tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_BASE__UINTSIZE_SLICE_UINT8 };
  l.val.Base.tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_SLICE__UINTSIZE_SLICE_UINT8;
  l.val.Base.val.Slice.ss = (Pulse_Lib_Slice_slice__slice_uint8){ .elt = a, .len = n };
  l.val.Base.val.Slice.count = n;
  return l;
}

static Pulse_Lib_Slice_slice__uint8 items_arr[] = { { (uint8_t *)"x", 1 }, { (uint8_t *)"yz", 2 } };

/* Msg { id 5, critical TRUE, color green, body inner: flag TRUE,
         pair { left 7, right 'ab' }, items { 'x', 'yz' } } */
static Msg msg1(void) {
  Msg m;
  memset(&m, 0, sizeof m);
  m.version.tag = SMALL_IMPL_MSG_VERSION_ABSENT;
  m.id = (ASN1_Pulse_Rel_asn1_int_impl){ .tag = ASN1_PULSE_REL_SMALL, .val = { .Small = 5 } };
  m.critical.tag = SMALL_IMPL_MSG_CRITICAL_PRESENT;
  m.critical.val.Msg_critical_present = true;
  m.color.tag = SMALL_IMPL_MSG_COLOR_PRESENT;
  m.color.val.Msg_color_present = 5;
  m.body.tag = SMALL_IMPL_ALT_INNER;
  m.body.val.Alt_inner.tag = SMALL_IMPL_INNER_FLAG;
  m.body.val.Alt_inner.val.Inner_flag = true;
  m.pair.tag = SMALL_IMPL_MSG_PAIR_PRESENT;
  m.pair.val.Msg_pair_present = (Pair){ .left = 7, .right = sl("ab") };
  m.pair.val.Msg_pair_present.note.tag = SMALL_IMPL_PAIR_NOTE_ABSENT;
  m.items = octs(items_arr, 2);
  m.extra.tag = SMALL_IMPL_MSG_EXTRA_ABSENT;
  return m;
}

static const uint8_t msg1_der[] = {
  0x30, 0x20,
  0x02, 0x01, 0x05,                                     /* id */
  0x01, 0x01, 0xff,                                     /* critical */
  0x0a, 0x01, 0x05,                                     /* color */
  0xa3, 0x03, 0x01, 0x01, 0xff,                         /* body [3] */
  0xa1, 0x07, 0x80, 0x01, 0x07, 0x81, 0x02, 0x61, 0x62, /* pair [1] */
  0x30, 0x07, 0x04, 0x01, 0x78, 0x04, 0x02, 0x79, 0x7a, /* items */
};

/* Msg { version v3, id -1, body name 'n', items { '' },
         extra { a 300, b 'u' } } */
static Msg msg2(void) {
  Msg m = msg1();
  m.version.tag = SMALL_IMPL_MSG_VERSION_PRESENT;
  m.version.val.Msg_version_present = 2;
  m.id.val.Small = -1;
  m.critical.tag = SMALL_IMPL_MSG_CRITICAL_ABSENT;
  m.color.tag = SMALL_IMPL_MSG_COLOR_ABSENT;
  m.body.tag = SMALL_IMPL_ALT_NAME;
  m.body.val.Alt_name = sl("n");
  m.pair.tag = SMALL_IMPL_MSG_PAIR_ABSENT;
  static Pulse_Lib_Slice_slice__uint8 empty[] = { { (uint8_t *)"", 0 } };
  m.items = octs(empty, 1);
  m.extra.tag = SMALL_IMPL_MSG_EXTRA_PRESENT;
  m.extra.val.Msg_extra_present = (Msg_extra){
    .a = { .tag = ASN1_PULSE_REL_SMALL, .val = { .Small = 300 } }, .b = sl("u") };
  return m;
}

static const uint8_t msg2_der[] = {
  0x30, 0x18,
  0x80, 0x01, 0x02,                                     /* version [0] */
  0x02, 0x01, 0xff,                                     /* id */
  0xa3, 0x03, 0x80, 0x01, 0x6e,                         /* body [3] name [0] */
  0x30, 0x02, 0x04, 0x00,                               /* items */
  0xa2, 0x07, 0x02, 0x02, 0x01, 0x2c, 0x0c, 0x01, 0x75, /* extra [2] */
};

/* msg1 with pair.note TRUE (an OPTIONAL SET component) */
static Msg msg3(void) {
  Msg m = msg1();
  m.pair.val.Msg_pair_present.note.tag = SMALL_IMPL_PAIR_NOTE_PRESENT;
  m.pair.val.Msg_pair_present.note.val.Pair_note_present = true;
  return m;
}

static const uint8_t msg3_der[] = {
  0x30, 0x23,
  0x02, 0x01, 0x05,
  0x01, 0x01, 0xff,
  0x0a, 0x01, 0x05,
  0xa3, 0x03, 0x01, 0x01, 0xff,
  0xa1, 0x0a, 0x80, 0x01, 0x07, 0x81, 0x02, 0x61, 0x62, 0x82, 0x01, 0xff, /* pair [1] */
  0x30, 0x07, 0x04, 0x01, 0x78, 0x04, 0x02, 0x79, 0x7a,
};

static void write_ok(const char *name, Msg x, const uint8_t *exp, size_t len) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Msg(x, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write: expected the DER bytes (result %d, %zu bytes)", name, (int)r, BUF - pos);
  pos = len - 1;
  Pulse_Lib_Slice_slice__uint8 s = { .elt = out, .len = len - 1 };
  CHECK(write_Msg(x, s, &pos) == ASN1_PULSE_JITWRITER_JIT_NO_SPACE,
        "%s: short buffer: expected NO_SPACE", name);
}

static void write_invalid(const char *name, Msg x) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Msg(x, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_INVALID, "%s: expected INVALID (%d)", name, (int)r);
}

static int validate(const uint8_t *in, size_t len) {
  Pulse_Lib_Slice_slice__uint8 s = { .elt = (uint8_t *)in, .len = len };
  size_t off = 0;
  return validate_Msg(s, &off) && off == len;
}

/* Names: SIZE on character strings counts characters, not bytes */

static Names names(const char *sh, const char *wide) {
  Names n;
  memset(&n, 0, sizeof n);
  n.short__ = sl(sh);
  n.wide = sl(wide);
  n.bmp.tag = SMALL_IMPL_NAMES_BMP_ABSENT;
  return n;
}

/* Names has KEEP-BYTES: its C type Names_kept pairs it with optional bytes,
   that the writers ignore */
static Names_kept kn(Names x) {
  Names_kept k;
  memset(&k, 0, sizeof k);
  k.value = x;
  k.raw.tag = SMALL_IMPL_NAMES_RAW_ABSENT;
  return k;
}

static int validate_names(const uint8_t *in, size_t len) {
  Pulse_Lib_Slice_slice__uint8 s = { .elt = (uint8_t *)in, .len = len };
  size_t off = 0;
  return validate_Names(s, &off) && off == len;
}

/* write `x`, compare with `exp`, then validate, parse and write back */
static void names_ok(const char *name, Names x, const uint8_t *exp, size_t len) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Names(kn(x), o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write: expected the DER bytes (result %d, %zu bytes)", name, (int)r, BUF - pos);
  CHECK(validate_names(exp, len), "%s: validate", name);
  Names_kept p = parse_Names((Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)exp, .len = len });
  CHECK(p.value.short__.len == x.short__.len && p.value.wide.len == x.wide.len && p.value.bmp.tag == x.bmp.tag,
        "%s: parse", name);
  CHECK(p.raw.tag == SMALL_IMPL_NAMES_RAW_PRESENT && p.raw.val.Names_raw_present.elt == exp &&
        p.raw.val.Names_raw_present.len == len, "%s: parse: kept bytes", name);
  pos = BUF;
  r = write_Names_typed(p, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write back", name);
  /* stale kept bytes are ignored by the writer */
  p.raw.val.Names_raw_present = sl("garbage");
  pos = BUF;
  r = write_Names(p, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, exp, len) == 0,
        "%s: write with stale kept bytes", name);
}

static void names_invalid(const char *name, Names x) {
  uint8_t out[BUF];
  size_t pos = BUF;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  ASN1_Pulse_JitWriter_jit_result r = write_Names(kn(x), o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_INVALID, "%s: expected INVALID (%d)", name, (int)r);
}

/* short "AB", wide "\u00e9x" (2 characters, 3 bytes) */
static const uint8_t names1_der[] = {
  0x30, 0x09, 0x13, 0x02, 0x41, 0x42, 0x0c, 0x03, 0xc3, 0xa9, 0x78
};
/* short "ABCD", wide "\u00e9\u00e9" (2 characters, 4 bytes), bmp "AB" */
static const uint8_t names2_der[] = {
  0x30, 0x12, 0x13, 0x04, 0x41, 0x42, 0x43, 0x44, 0x0c, 0x04, 0xc3, 0xa9, 0xc3, 0xa9,
  0x1e, 0x04, 0x00, 0x41, 0x00, 0x42
};

static void test_names(void) {
  names_ok("names1", names("AB", "\xc3\xa9x"), names1_der, sizeof names1_der);
  Names n = names("ABCD", "\xc3\xa9\xc3\xa9");
  n.bmp.tag = SMALL_IMPL_NAMES_BMP_PRESENT;
  n.bmp.val.Names_bmp_present = (Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)"\0A\0B", .len = 4 };
  names_ok("names2", n, names2_der, sizeof names2_der);

  names_invalid("short: 5 characters", names("ABCDE", "x"));
  names_invalid("short: empty", names("", "x"));
  names_invalid("wide: 3 characters in 3 bytes", names("A", "xyz"));
  names_invalid("wide: 3 characters in 6 bytes", names("A", "\xc3\xa9\xc3\xa9\xc3\xa9"));
  n.bmp.val.Names_bmp_present.len = 2;
  names_invalid("bmp: 1 character", n);

  uint8_t in[sizeof names2_der];
  memcpy(in, names2_der, sizeof in);
  in[12] = 0x41; in[13] = 0x42; /* wide "\u00e9AB": 3 characters */
  CHECK(!validate_names(in, sizeof in), "wide: 3 characters: expected rejection");
  memcpy(in, names2_der, sizeof in);
  in[7] = 0x2a; /* short "ABC*": not printable */
  CHECK(!validate_names(in, sizeof in), "short: not printable: expected rejection");
  static const uint8_t short5[] = {
    0x30, 0x0a, 0x13, 0x05, 0x41, 0x42, 0x43, 0x44, 0x45, 0x0c, 0x01, 0x78
  };
  CHECK(validate_names(short5, sizeof short5) == 0, "short: 5 characters: expected rejection");
  static const uint8_t bmp1[] = {
    0x30, 0x0a, 0x13, 0x01, 0x41, 0x0c, 0x01, 0x78, 0x1e, 0x02, 0x00, 0x41
  };
  CHECK(validate_names(bmp1, sizeof bmp1) == 0, "bmp: 1 character: expected rejection");
  static const uint8_t one[] = { 0x30, 0x06, 0x13, 0x01, 0x41, 0x0c, 0x01, 0x78 };
  CHECK(validate_names(one, sizeof one), "short \"A\", wide \"x\": validate");
}

/* Wrapper: Names nested (kept bytes point into the input), also under an
   EXPLICIT tag in an OPTIONAL component */
static const uint8_t wrapper_der[] = {
  0x30, 0x24, 0x02, 0x01, 0x03,
  0x30, 0x09, 0x13, 0x02, 0x41, 0x42, 0x0c, 0x03, 0xc3, 0xa9, 0x78,
  0xa0, 0x14,
  0x30, 0x12, 0x13, 0x04, 0x41, 0x42, 0x43, 0x44, 0x0c, 0x04, 0xc3, 0xa9, 0xc3, 0xa9,
  0x1e, 0x04, 0x00, 0x41, 0x00, 0x42
};

static void test_wrapper(void) {
  uint8_t out[BUF];
  size_t pos = BUF;
  size_t len = sizeof wrapper_der;
  Pulse_Lib_Slice_slice__uint8 o = { .elt = out, .len = BUF };
  Pulse_Lib_Slice_slice__uint8 in = { .elt = (uint8_t *)wrapper_der, .len = len };
  Wrapper w;
  memset(&w, 0, sizeof w);
  w.n = 3;
  w.names = kn(names("AB", "\xc3\xa9x"));
  Names n2 = names("ABCD", "\xc3\xa9\xc3\xa9");
  n2.bmp.tag = SMALL_IMPL_NAMES_BMP_PRESENT;
  n2.bmp.val.Names_bmp_present = (Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)"\0A\0B", .len = 4 };
  w.alt.tag = SMALL_IMPL_WRAPPER_ALT_PRESENT;
  w.alt.val.Wrapper_alt_present = kn(n2);
  ASN1_Pulse_JitWriter_jit_result r = write_Wrapper(w, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, wrapper_der, len) == 0,
        "wrapper: write (result %d, %zu bytes)", (int)r, BUF - pos);
  size_t off = 0;
  CHECK(validate_Wrapper(in, &off) && off == len, "wrapper: validate");
  Wrapper p = parse_Wrapper(in);
  CHECK(p.n == 3, "wrapper: parse n");
  CHECK(p.names.raw.tag == SMALL_IMPL_NAMES_RAW_PRESENT &&
        p.names.raw.val.Names_raw_present.elt == wrapper_der + 5 &&
        p.names.raw.val.Names_raw_present.len == 11, "wrapper: names kept bytes");
  CHECK(p.alt.tag == SMALL_IMPL_WRAPPER_ALT_PRESENT &&
        p.alt.val.Wrapper_alt_present.raw.tag == SMALL_IMPL_NAMES_RAW_PRESENT &&
        p.alt.val.Wrapper_alt_present.raw.val.Names_raw_present.elt == wrapper_der + 18 &&
        p.alt.val.Wrapper_alt_present.raw.val.Names_raw_present.len == 20 &&
        p.alt.val.Wrapper_alt_present.value.bmp.tag == SMALL_IMPL_NAMES_BMP_PRESENT, "wrapper: alt kept bytes");
  pos = BUF;
  r = write_Wrapper_typed(p, o, &pos);
  CHECK(r == ASN1_PULSE_JITWRITER_JIT_OK && pos == BUF - len && memcmp(out + pos, wrapper_der, len) == 0,
        "wrapper: write back");
}

int main(void) {
  custard_init_globals();
  Msg m1 = msg1(), m2 = msg2(), m3 = msg3();
  write_ok("msg1", m1, msg1_der, sizeof msg1_der);
  write_ok("msg2", m2, msg2_der, sizeof msg2_der);
  write_ok("msg3", m3, msg3_der, sizeof msg3_der);
  test_names();
  test_wrapper();

  /* a DEFAULT component present with its default value is omitted (DER) */
  Msg bad = msg1();
  bad.version.tag = SMALL_IMPL_MSG_VERSION_PRESENT;
  bad.version.val.Msg_version_present = 0;
  write_ok("version = DEFAULT", bad, msg1_der, sizeof msg1_der);
  bad = msg2();
  bad.critical.tag = SMALL_IMPL_MSG_CRITICAL_PRESENT;
  bad.critical.val.Msg_critical_present = false;
  write_ok("critical = DEFAULT", bad, msg2_der, sizeof msg2_der);

  /* not encodable: values outside of the constraints */
  bad = msg1();
  bad.color.val.Msg_color_present = 3;
  write_invalid("color not in ENUMERATED", bad);
  bad = msg1();
  bad.pair.val.Msg_pair_present.left = 256;
  write_invalid("left not in (0..255)", bad);
  bad = msg1();
  bad.pair.val.Msg_pair_present.right = sl("abcde");
  write_invalid("right not in SIZE (1..4)", bad);
  bad = msg1();
  bad.items = octs(items_arr, 0);
  bad.items.val.Base.tag = LOWPARSE_PULSEPARSE_ITERATOR_TYPE_EMPTY__UINTSIZE_SLICE_UINT8;
  write_invalid("items SIZE (1..MAX) empty", bad);

  CHECK(validate(msg1_der, sizeof msg1_der), "msg1: validate");
  CHECK(validate(msg2_der, sizeof msg2_der), "msg2: validate");
  CHECK(validate(msg3_der, sizeof msg3_der), "msg3: validate");
  {
    /* DER: critical encoded with its DEFAULT value */
    uint8_t in[sizeof msg1_der];
    memcpy(in, msg1_der, sizeof in);
    in[7] = 0x00;
    CHECK(!validate(in, sizeof in), "critical = FALSE: expected rejection");
    /* DER: SET components out of tag order */
    static const uint8_t swapped[] = { 0x81, 0x02, 0x61, 0x62, 0x80, 0x01, 0x07 };
    memcpy(in, msg1_der, sizeof in);
    memcpy(in + 18, swapped, sizeof swapped);
    CHECK(!validate(in, sizeof in), "SET out of order: expected rejection");
    /* truncated */
    CHECK(!validate(msg1_der, sizeof msg1_der - 1), "truncated: expected rejection");
  }

  Msg p = parse_Msg((Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)msg1_der, .len = sizeof msg1_der });
  CHECK(p.version.tag == SMALL_IMPL_MSG_VERSION_ABSENT, "parse msg1: version");
  CHECK(p.id.tag == ASN1_PULSE_REL_SMALL && p.id.val.Small == 5, "parse msg1: id");
  CHECK(p.critical.tag == SMALL_IMPL_MSG_CRITICAL_PRESENT && p.critical.val.Msg_critical_present, "parse msg1: critical");
  CHECK(p.color.tag == SMALL_IMPL_MSG_COLOR_PRESENT && p.color.val.Msg_color_present == 5, "parse msg1: color");
  CHECK(p.body.tag == SMALL_IMPL_ALT_INNER && p.body.val.Alt_inner.tag == SMALL_IMPL_INNER_FLAG &&
        p.body.val.Alt_inner.val.Inner_flag, "parse msg1: body");
  CHECK(p.pair.tag == SMALL_IMPL_MSG_PAIR_PRESENT && p.pair.val.Msg_pair_present.left == 7 &&
        p.pair.val.Msg_pair_present.right.len == 2 &&
        p.pair.val.Msg_pair_present.right.elt == msg1_der + 23, "parse msg1: pair (zero-copy)");
  CHECK(p.pair.val.Msg_pair_present.note.tag == SMALL_IMPL_PAIR_NOTE_ABSENT, "parse msg1: pair.note");
  CHECK(p.extra.tag == SMALL_IMPL_MSG_EXTRA_ABSENT, "parse msg1: extra");
  /* the parsed value can be written back */
  write_ok("msg1 parsed", p, msg1_der, sizeof msg1_der);

  p = parse_Msg((Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)msg2_der, .len = sizeof msg2_der });
  CHECK(p.version.tag == SMALL_IMPL_MSG_VERSION_PRESENT && p.version.val.Msg_version_present == 2, "parse msg2: version");
  CHECK(p.critical.tag == SMALL_IMPL_MSG_CRITICAL_ABSENT, "parse msg2: critical");
  CHECK(p.body.tag == SMALL_IMPL_ALT_NAME && p.body.val.Alt_name.len == 1 && p.body.val.Alt_name.elt[0] == 'n', "parse msg2: body");
  CHECK(p.extra.tag == SMALL_IMPL_MSG_EXTRA_PRESENT && p.extra.val.Msg_extra_present.a.val.Small == 300 &&
        p.extra.val.Msg_extra_present.b.len == 1, "parse msg2: extra");
  write_ok("msg2 parsed", p, msg2_der, sizeof msg2_der);

  p = parse_Msg((Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)msg3_der, .len = sizeof msg3_der });
  CHECK(p.pair.tag == SMALL_IMPL_MSG_PAIR_PRESENT &&
        p.pair.val.Msg_pair_present.note.tag == SMALL_IMPL_PAIR_NOTE_PRESENT &&
        p.pair.val.Msg_pair_present.note.val.Pair_note_present, "parse msg3: pair.note");
  write_ok("msg3 parsed", p, msg3_der, sizeof msg3_der);

  if (fails) { printf("small test: %d failures\n", fails); return 1; }
  printf("small test: OK\n");
  return 0;
}
