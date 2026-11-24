/* Test driver for the C output style options (--hoist_locals,
   --init_locals, --line_comments). The same driver is linked against
   every variant of the generated code, so these options must not change
   the behavior of the validator. */

#include "LocalsWrapper.h"

#include <stdio.h>
#include <string.h>

static unsigned error_count = 0;

void LocalsEverParseError(const char *StructName,
                          const char *FieldName,
                          const char *Reason) {
  (void) StructName;
  (void) FieldName;
  (void) Reason;
  error_count++;
}

static void put_le16(uint8_t *buf, size_t off, uint16_t v) {
  buf[off + 0] = (uint8_t) (v & 0xff);
  buf[off + 1] = (uint8_t) ((v >> 8) & 0xff);
}

static void put_le32(uint8_t *buf, size_t off, uint32_t v) {
  buf[off + 0] = (uint8_t) (v & 0xff);
  buf[off + 1] = (uint8_t) ((v >> 8) & 0xff);
  buf[off + 2] = (uint8_t) ((v >> 16) & 0xff);
  buf[off + 3] = (uint8_t) ((v >> 24) & 0xff);
}

/* Build a message with the given header and count, and validate its
   first `8 + avail` bytes, where `avail` may differ from `len` and may be
   negative to cut the fixed-size header. */
static int check(const char *name, int expected, uint16_t tag, uint16_t len,
                 uint32_t count, uint32_t accum_in, uint32_t accum_out,
                 int avail) {
  uint8_t buf[8 + 128];
  uint32_t accum = accum_in;
  uint16_t out_tag = 0;
  unsigned errors_before = error_count;
  int ok;
  memset(buf, 0xaa, sizeof(buf));
  put_le16(buf, 0, tag);
  put_le16(buf, 2, len);
  put_le32(buf, 4, count);
  ok = LocalsCheckMsg(&accum, &out_tag, buf, (uint32_t) (8 + avail)) ? 1 : 0;
  if (ok != expected) {
    fprintf(stderr, "FAIL %s: expected %s\n", name,
            expected ? "success" : "failure");
    return 1;
  }
  if (ok && (accum != accum_out || out_tag != tag)) {
    fprintf(stderr, "FAIL %s: wrong outputs (accum=%u, tag=%u)\n", name,
            (unsigned) accum, (unsigned) out_tag);
    return 1;
  }
  if (!ok && error_count == errors_before) {
    fprintf(stderr, "FAIL %s: error handler not called\n", name);
    return 1;
  }
  return 0;
}

int main(void) {
  int rc = 0;
  rc |= check("bytes", 1, 1, 3, 5, 10, 15, 3);
  rc |= check("words", 1, 2, 8, 1, 0, 1, 8);
  rc |= check("halves", 1, 7, 4, 2, 0, 2, 4);
  rc |= check("empty payload", 1, 1, 0, 1, 0, 1, 0);
  rc |= check("words not a multiple of 4", 0, 2, 3, 1, 0, 0, 3);
  rc |= check("halves not a multiple of 2", 0, 9, 5, 1, 0, 0, 5);
  rc |= check("len too large", 0, 1, 65, 1, 0, 0, 65);
  rc |= check("count zero", 0, 1, 1, 0, 0, 0, 1);
  rc |= check("accumulator overflow", 0, 1, 1, 5, 0xfffffffeU, 0, 1);
  rc |= check("payload too short", 0, 1, 4, 1, 0, 0, 3);
  rc |= check("header too short", 0, 1, 0, 1, 0, 0, -2);
  if (rc == 0) {
    printf("c_style_options: all checks passed\n");
  }
  return rc;
}
