/* Test driver for the `Complete' entrypoint wrappers.

   The plain `TestCheck<T>' wrappers only check that validation
   succeeded, so they accept an input buffer with trailing bytes.  The
   `TestCheckComplete<T>' wrappers additionally check that the
   validator consumed the whole buffer. */

#include "TestWrapper.h"

#include <stdio.h>
#include <string.h>

static int error_count = 0;

/* Called by the generated wrapper when validation fails. */
void TestEverParseError(const char *StructName,
                        const char *FieldName,
                        const char *Reason) {
  (void) StructName;
  (void) FieldName;
  (void) Reason;
  ++error_count;
}

static void put_le32(uint8_t *buf, size_t off, uint32_t v) {
  buf[off + 0] = (uint8_t) (v & 0xff);
  buf[off + 1] = (uint8_t) ((v >> 8) & 0xff);
  buf[off + 2] = (uint8_t) ((v >> 16) & 0xff);
  buf[off + 3] = (uint8_t) ((v >> 24) & 0xff);
}

int main(void) {
  int rc = 0;

  /* POINT is exactly 8 bytes. */
  uint8_t buf[12];
  memset(buf, 0, sizeof(buf));
  put_le32(buf, 0, 10);
  put_le32(buf, 4, 5);

  /* 1. Exact-size input: both wrappers accept. */
  if (!TestCheckPoint(buf, 8)) {
    fprintf(stderr, "FAIL: exact-size input rejected by TestCheckPoint\n");
    rc = 1;
  }
  if (!TestCheckCompletePoint(buf, 8)) {
    fprintf(stderr, "FAIL: exact-size input rejected by TestCheckCompletePoint\n");
    rc = 1;
  }

  /* 2. Trailing bytes: the plain wrapper accepts, the complete one
        rejects and reports an error. */
  if (!TestCheckPoint(buf, sizeof(buf))) {
    fprintf(stderr, "FAIL: input with trailing bytes rejected by TestCheckPoint\n");
    rc = 1;
  }
  error_count = 0;
  if (TestCheckCompletePoint(buf, sizeof(buf))) {
    fprintf(stderr, "FAIL: input with trailing bytes accepted by TestCheckCompletePoint\n");
    rc = 1;
  }
  if (error_count != 1) {
    fprintf(stderr, "FAIL: expected exactly one error report, got %d\n", error_count);
    rc = 1;
  }

  /* 3. Too-short input: both wrappers reject. */
  if (TestCheckPoint(buf, 4)) {
    fprintf(stderr, "FAIL: short input accepted by TestCheckPoint\n");
    rc = 1;
  }
  if (TestCheckCompletePoint(buf, 4)) {
    fprintf(stderr, "FAIL: short input accepted by TestCheckCompletePoint\n");
    rc = 1;
  }

  /* 4. Named entrypoint: HEADER is exactly 1 byte, and its
        complete-check wrapper is named by suffixing `Complete'. */
  if (!CheckHeader(buf, 1)) {
    fprintf(stderr, "FAIL: exact-size input rejected by CheckHeader\n");
    rc = 1;
  }
  if (!CheckHeaderComplete(buf, 1)) {
    fprintf(stderr, "FAIL: exact-size input rejected by CheckHeaderComplete\n");
    rc = 1;
  }
  if (!CheckHeader(buf, sizeof(buf))) {
    fprintf(stderr, "FAIL: input with trailing bytes rejected by CheckHeader\n");
    rc = 1;
  }
  if (CheckHeaderComplete(buf, sizeof(buf))) {
    fprintf(stderr, "FAIL: input with trailing bytes accepted by CheckHeaderComplete\n");
    rc = 1;
  }

  if (rc == 0) {
    printf("check_complete test: all checks passed\n");
  }
  return rc;
}
