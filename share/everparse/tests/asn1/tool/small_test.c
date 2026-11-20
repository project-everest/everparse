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

/* Lazy iteration over the components of a SEQUENCE (ASN1.Pulse.SeqIter):
   the indices of the present components, each read on demand */
static void seq_iter_msg(const char *name, const uint8_t *der, size_t len, const char *exp) {
  char got[16] = { 0 };
  int n = 0;
  ASN1_Pulse_SeqIter_seq_iter it = Msg_seq_start((Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)der, .len = len });
  while (!Msg_seq_is_empty(it) && n < 15) {
    ASN1_Pulse_SeqIter_seq_item x = Msg_seq_next(&it);
    CHECK(x.bytes.elt > der && x.bytes.elt + x.bytes.len <= der + len, "%s: item bytes", name);
    got[n++] = (char)('0' + x.comp);
    switch (x.comp) {
    case Msg_version_index: {
      Msg_version_opt v = Msg_version_get(x);
      CHECK(v.tag == SMALL_IMPL_MSG_VERSION_PRESENT && v.val.Msg_version_present == 2, "%s: version", name);
      break; }
    case Msg_id_index: {
      ASN1_Pulse_Rel_asn1_int_impl v = Msg_id_get(x);
      CHECK(v.tag == ASN1_PULSE_REL_SMALL && (v.val.Small == 5 || v.val.Small == -1), "%s: id", name);
      break; }
    case Msg_critical_index: {
      Msg_critical_opt v = Msg_critical_get(x);
      CHECK(v.tag == SMALL_IMPL_MSG_CRITICAL_PRESENT && v.val.Msg_critical_present, "%s: critical", name);
      break; }
    case Msg_color_index: {
      Msg_color_opt v = Msg_color_get(x);
      CHECK(v.tag == SMALL_IMPL_MSG_COLOR_PRESENT && v.val.Msg_color_present == 5, "%s: color", name);
      break; }
    case Msg_body_index: {
      Alt v = Msg_body_get(x);
      CHECK(v.tag == SMALL_IMPL_ALT_INNER || (v.tag == SMALL_IMPL_ALT_NAME && v.val.Alt_name.elt[0] == 'n'), "%s: body", name);
      break; }
    case Msg_pair_index: {
      Msg_pair_opt v = Msg_pair_get(x);
      CHECK(v.tag == SMALL_IMPL_MSG_PAIR_PRESENT && v.val.Msg_pair_present.left == 7, "%s: pair", name);
      break; }
    case Msg_items_index: {
      ASN1_Pulse_ListIter_iter li = Msg_items_iter_start(Msg_items_get(x));
      CHECK(Msg_items_iter_length(li) >= 1, "%s: items", name);
      break; }
    case Msg_extra_index: {
      Msg_extra_opt v = Msg_extra_get(x);
      CHECK(v.tag == SMALL_IMPL_MSG_EXTRA_PRESENT && v.val.Msg_extra_present.a.val.Small == 300, "%s: extra", name);
      break; }
    default:
      CHECK(0, "%s: unexpected index %u", name, (unsigned)x.comp);
    }
  }
  CHECK(strcmp(got, exp) == 0, "%s: components %s, expected %s", name, got, exp);
}

/* Iterate over the components of a Pair (a SET), in encoding order */
static void set_iter_pair(const char *name, const uint8_t *der, size_t len, const char *exp) {
  char got[8] = { 0 };
  int n = 0;
  ASN1_Pulse_SeqIter_seq_iter it = Pair_set_start((Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)der, .len = len });
  while (!Pair_set_is_empty(it) && n < 7) {
    ASN1_Pulse_SeqIter_seq_item x = Pair_set_next(&it);
    got[n++] = (char)('0' + x.comp);
    switch (x.comp) {
    case Pair_left_index:
      CHECK(Pair_left_get(x) == 7, "%s: left", name);
      break;
    case Pair_right_index: {
      Pulse_Lib_Slice_slice__uint8 v = Pair_right_get(x);
      CHECK(v.len == 2 && v.elt[0] == 'a' && v.elt[1] == 'b', "%s: right", name);
      break; }
    case Pair_note_index: {
      Pair_note_opt v = Pair_note_get(x);
      CHECK(v.tag == SMALL_IMPL_PAIR_NOTE_PRESENT && v.val.Pair_note_present, "%s: note", name);
      break; }
    default:
      CHECK(0, "%s: unexpected index %u", name, (unsigned)x.comp);
    }
  }
  CHECK(strcmp(got, exp) == 0, "%s: components %s, expected %s", name, got, exp);
}

static const uint8_t pair_der[] = { 0x31, 0x07, 0x80, 0x01, 0x07, 0x81, 0x02, 0x61, 0x62 };
static const uint8_t pair_note_der[] = { 0x31, 0x0a, 0x80, 0x01, 0x07, 0x81, 0x02, 0x61, 0x62, 0x82, 0x01, 0xff };

static void test_seq_iter(void) {
  seq_iter_msg("seq_iter msg1", msg1_der, sizeof msg1_der, "123456");
  seq_iter_msg("seq_iter msg2", msg2_der, sizeof msg2_der, "01467");
  set_iter_pair("set_iter pair", pair_der, sizeof pair_der, "01");
  set_iter_pair("set_iter pair note", pair_note_der, sizeof pair_note_der, "012");
  /* a nested SEQUENCE: from the bytes of the item */
  ASN1_Pulse_SeqIter_seq_iter it = Wrapper_seq_start((Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)wrapper_der, .len = sizeof wrapper_der });
  ASN1_Pulse_SeqIter_seq_item x = Wrapper_seq_next(&it);
  CHECK(x.comp == Wrapper_n_index && Wrapper_n_get(x) == 3, "seq_iter wrapper: n");
  x = Wrapper_seq_next(&it);
  CHECK(x.comp == Wrapper_names_index, "seq_iter wrapper: names");
  ASN1_Pulse_SeqIter_seq_iter ni = Names_seq_start(x.bytes);
  ASN1_Pulse_SeqIter_seq_item y = Names_seq_next(&ni);
  Pulse_Lib_Slice_slice__uint8 sh = Names_short_get(y);
  CHECK(y.comp == Names_short_index && sh.len == 2 && sh.elt == wrapper_der + 9, "seq_iter wrapper: names.short (zero-copy)");
  y = Names_seq_next(&ni);
  CHECK(y.comp == Names_wide_index && Names_seq_is_empty(ni), "seq_iter wrapper: names end");
  Names_kept nk = Wrapper_names_get(x);
  CHECK(nk.raw.tag == SMALL_IMPL_NAMES_RAW_PRESENT && nk.raw.val.Names_raw_present.elt == wrapper_der + 5, "seq_iter wrapper: names kept");
  x = Wrapper_seq_next(&it);
  CHECK(x.comp == Wrapper_alt_index && Wrapper_seq_is_empty(it), "seq_iter wrapper: alt");
  Wrapper_alt_opt a = Wrapper_alt_get(x);
  CHECK(a.tag == SMALL_IMPL_WRAPPER_ALT_PRESENT && a.val.Wrapper_alt_present.value.bmp.tag == SMALL_IMPL_NAMES_BMP_PRESENT, "seq_iter wrapper: alt value");
}

int main(void) {
  Msg m1 = msg1(), m2 = msg2(), m3 = msg3();
  write_ok("msg1", m1, msg1_der, sizeof msg1_der);
  write_ok("msg2", m2, msg2_der, sizeof msg2_der);
  write_ok("msg3", m3, msg3_der, sizeof msg3_der);
  test_names();
  test_wrapper();
  test_seq_iter();

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
  {
    /* iterate over the parsed items (zero-copy) */
    ASN1_Pulse_ListIter_iter it = Msg_items_iter_start(p.items);
    CHECK(Msg_items_iter_length(it) == 2 && !Msg_items_iter_is_empty(it), "iter msg1: length");
    Pulse_Lib_Slice_slice__uint8 e = Msg_items_iter_next(&it);
    CHECK(e.len == 1 && e.elt[0] == 'x' && e.elt > msg1_der && e.elt < msg1_der + sizeof msg1_der, "iter msg1: items[0]");
    CHECK(Msg_items_iter_length(it) == 1, "iter msg1: length after next");
    e = Msg_items_iter_next(&it);
    CHECK(e.len == 2 && e.elt[0] == 'y' && e.elt[1] == 'z', "iter msg1: items[1]");
    CHECK(Msg_items_iter_is_empty(it), "iter msg1: end");
  }
  /* the parsed value can be written back */
  write_ok("msg1 parsed", p, msg1_der, sizeof msg1_der);
  {
    /* writer-form iteration (ListIterW) over the parsed items */
    LowParse_PulseParse_Iterator_Type_iterator__uintsize_slice_uint8 w = Msg_items_witer_start(p.items);
    CHECK(!Msg_items_witer_is_empty(w), "witer msg1: not empty");
    Pulse_Lib_Slice_slice__uint8 e = Msg_items_witer_next(&w);
    CHECK(e.len == 1 && e.elt[0] == 'x', "witer msg1: items[0]");
    e = Msg_items_witer_next(&w);
    CHECK(e.len == 2 && e.elt[0] == 'y' && e.elt[1] == 'z', "witer msg1: items[1]");
    CHECK(Msg_items_witer_is_empty(w), "witer msg1: end");
    /* items built from arrays, appended (with an empty list in between),
       iterated, then written back */
    uint8_t x[] = { 'x' }, yz[] = { 'y', 'z' };
    Pulse_Lib_Slice_slice__uint8 a1[] = { { .elt = x, .len = 1 } }, a2[] = { { .elt = yz, .len = 2 } };
    LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 l1 =
      Msg_items_of_slice((Pulse_Lib_Slice_slice__slice_uint8){ .elt = a1, .len = 1 });
    LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 l2 =
      Msg_items_of_slice((Pulse_Lib_Slice_slice__slice_uint8){ .elt = a2, .len = 1 });
    LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 le = Msg_items_empty();
    LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 l1e = Msg_items_append(&l1, &le);
    LowParse_PulseParse_Iterator_Type_mixed_list__uintsize_slice_uint8 l = Msg_items_append(&l1e, &l2);
    w = Msg_items_witer_start(l);
    e = Msg_items_witer_next(&w);
    CHECK(e.elt == x && e.len == 1, "witer built: items[0]");
    e = Msg_items_witer_next(&w);
    CHECK(e.elt == yz && e.len == 2 && Msg_items_witer_is_empty(w), "witer built: items[1]");
    Msg q = p;
    q.items = l;
    write_ok("msg1 built items", q, msg1_der, sizeof msg1_der);
  }

  p = parse_Msg((Pulse_Lib_Slice_slice__uint8){ .elt = (uint8_t *)msg2_der, .len = sizeof msg2_der });
  CHECK(p.version.tag == SMALL_IMPL_MSG_VERSION_PRESENT && p.version.val.Msg_version_present == 2, "parse msg2: version");
  CHECK(p.critical.tag == SMALL_IMPL_MSG_CRITICAL_ABSENT, "parse msg2: critical");
  CHECK(p.body.tag == SMALL_IMPL_ALT_NAME && p.body.val.Alt_name.len == 1 && p.body.val.Alt_name.elt[0] == 'n', "parse msg2: body");
  CHECK(p.extra.tag == SMALL_IMPL_MSG_EXTRA_PRESENT && p.extra.val.Msg_extra_present.a.val.Small == 300 &&
        p.extra.val.Msg_extra_present.b.len == 1, "parse msg2: extra");
  {
    ASN1_Pulse_ListIter_iter it = Msg_items_iter_start(p.items);
    CHECK(Msg_items_iter_length(it) == 1, "iter msg2: length");
    Pulse_Lib_Slice_slice__uint8 e = Msg_items_iter_next(&it);
    CHECK(e.len == 0 && Msg_items_iter_is_empty(it), "iter msg2: items[0]");
  }
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
