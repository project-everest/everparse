/* Test driver for --use_error_handler_macro.  Runs the generated
   validator on a passing input, on an input that violates the
   constraint, and on an input that is too short.  In the latter two
   cases the validator invokes EVERPARSE_ERROR_HANDLER_MACRO defined
   in MyErrorHandlerMacro.h. */

#include "TestWrapper.h"

#include <stdio.h>
#include <string.h>

/* Forward-declared by the EverParse-generated wrapper.  It is invoked
   only if the dynamic error handler fills the EVERPARSE_ERROR_FRAME,
   which our macro intentionally does not do, so this function is
   never called in practice.  We still provide it to satisfy the
   linker. */
void TestEverParseError(const char *StructName,
                        const char *FieldName,
                        const char *Reason) {
  (void) StructName;
  (void) FieldName;
  (void) Reason;
}

/* Helper that writes a little-endian uint32_t into buf at offset off. */
static void put_le32(uint8_t *buf, size_t off, uint32_t v) {
  buf[off + 0] = (uint8_t) (v & 0xff);
  buf[off + 1] = (uint8_t) ((v >> 8) & 0xff);
  buf[off + 2] = (uint8_t) ((v >> 16) & 0xff);
  buf[off + 3] = (uint8_t) ((v >> 24) & 0xff);
}

int main(void) {
  int rc = 0;

  /* 1. Well-formed input: x=10, y=5; constraint y <= x holds. */
  uint8_t ok[8];
  put_le32(ok, 0, 10);
  put_le32(ok, 4, 5);
  if (!TestCheckPoint(ok, sizeof(ok))) {
    fprintf(stderr, "FAIL: expected valid input to be accepted\n");
    rc = 1;
  }

  /* 2. Constraint violation: x=1, y=2; y <= x is false.  The macro
        should be invoked. */
  uint8_t bad[8];
  put_le32(bad, 0, 1);
  put_le32(bad, 4, 2);
  if (TestCheckPoint(bad, sizeof(bad))) {
    fprintf(stderr, "FAIL: expected constraint-violating input to be rejected\n");
    rc = 1;
  }

  /* 3. Too-short input: only 4 bytes, validator wants 8.  The macro
        should be invoked for the not-enough-data error. */
  uint8_t shortbuf[4] = {0};
  if (TestCheckPoint(shortbuf, sizeof(shortbuf))) {
    fprintf(stderr, "FAIL: expected short input to be rejected\n");
    rc = 1;
  }

  if (rc == 0) {
    printf("use_error_handler_macro test: all checks passed\n");
  }
  return rc;
}
