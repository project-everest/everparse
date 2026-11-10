/* Test driver for the {:error-code ...} 3D field annotation. Calls the
   generated validators directly with an error handler that records the
   error code, and checks that the validator status and the code passed
   to the handler are the user-defined codes from src/Test.3d. */

#include "Test.h"
#include "TestWrapper.h"

#include <stdio.h>
#include <string.h>

static int handler_calls;
static uint8_t first_code;
static const char *first_reason;
static const char *first_field;

/* Invoked by the TestCheck* wrappers on failure; unused here except to
   check that the wrapper reports the reason for the user-defined code. */
static const char *wrapper_reason;
void TestEverParseError(const char *StructName,
                        const char *FieldName,
                        const char *Reason) {
  (void) StructName;
  (void) FieldName;
  wrapper_reason = Reason;
}

/* The handler is called once per enclosing type, innermost first: record
   the first call, and check that all calls agree on the code. */
static uint8_t all_codes_agree;
static void handler(const char *TypeName, const char *FieldName,
                    const char *ErrorReason, uint8_t ErrorCode,
                    uint8_t *Context, uint8_t *Base, size_t Length,
                    size_t *Position, uint64_t StartPosition) {
  (void) TypeName; (void) Context; (void) Base; (void) Length;
  (void) Position; (void) StartPosition;
  if (handler_calls == 0) {
    first_code = ErrorCode;
    first_reason = ErrorReason;
    first_field = FieldName;
  } else if (ErrorCode != first_code) {
    all_codes_agree = 0;
  }
  handler_calls++;
}

static void reset(void) {
  handler_calls = 0;
  first_code = 0;
  first_reason = NULL;
  first_field = NULL;
  all_codes_agree = 1;
  wrapper_reason = NULL;
}

static int rc = 0;

static void check(const char *name, uint8_t status, uint8_t expected) {
  const char *expected_reason =
    expected >= 128 ? "user-defined constraint failed" : "constraint failed";
  if (status != expected) {
    fprintf(stderr, "FAIL %s: expected status %u, got %u\n",
            name, (unsigned) expected, (unsigned) status);
    rc = 1;
    return;
  }
  if (expected == EVERPARSE_SUCCESS) {
    if (handler_calls != 0) {
      fprintf(stderr, "FAIL %s: error handler called on success\n", name);
      rc = 1;
    }
    return;
  }
  if (handler_calls == 0 || first_code != expected || !all_codes_agree) {
    fprintf(stderr, "FAIL %s: expected error handler code %u, got %u (%d calls)\n",
            name, (unsigned) expected, (unsigned) first_code, handler_calls);
    rc = 1;
    return;
  }
  if (strcmp(first_reason, expected_reason) != 0 ||
      strcmp(EverParseErrorReasonOfResult(status), expected_reason) != 0) {
    fprintf(stderr, "FAIL %s: unexpected reason %s\n", name, first_reason);
    rc = 1;
    return;
  }
  printf("%s: status %u, field %s, reason \"%s\"\n",
         name, (unsigned) status, first_field, first_reason);
}

static uint8_t header(uint8_t version, uint8_t kind, uint8_t flags) {
  uint8_t buf[3] = { version, kind, flags };
  size_t pos = 0;
  reset();
  return TestValidateHeader(NULL, handler, buf, sizeof(buf), &pos);
}

static uint8_t bits(uint8_t a, uint8_t b, uint8_t c) {
  uint8_t buf[1] = { (uint8_t) (a | (b << 2) | (c << 5)) };
  size_t pos = 0;
  reset();
  return TestValidateBits(NULL, handler, buf, sizeof(buf), &pos);
}

static void put_le32(uint8_t *buf, uint32_t v) {
  buf[0] = (uint8_t) v;
  buf[1] = (uint8_t) (v >> 8);
  buf[2] = (uint8_t) (v >> 16);
  buf[3] = (uint8_t) (v >> 24);
}

static uint32_t dep_out;
static uint8_t dep(uint32_t len, uint32_t tag) {
  uint8_t buf[16] = { 0 };
  size_t pos = 0;
  put_le32(buf, len);
  put_le32(buf + 4 + (len <= 4 ? len : 0), tag);
  reset();
  dep_out = 0;
  return TestValidateDep(&dep_out, NULL, handler, buf, 8 + (len <= 4 ? len : 0), &pos);
}

static uint8_t paint(uint8_t color) {
  uint8_t buf[1] = { color };
  size_t pos = 0;
  reset();
  return TestValidatePaint(NULL, handler, buf, sizeof(buf), &pos);
}

int main(void) {
  check("Header ok", header(1, 3, 0), EVERPARSE_SUCCESS);
  check("Header version", header(2, 0, 0), 200);
  check("Header kind (#define)", header(1, 4, 0), 201);
  check("Header flags (default)", header(1, 0, 1), EVERPARSE_ERROR_CONSTRAINT_FAILED);
  /* The first failing field determines the code */
  check("Header version and kind", header(2, 4, 1), 200);

  check("Bits ok", bits(1, 4, 6), EVERPARSE_SUCCESS);
  check("Bits a", bits(0, 0, 0), 128);
  check("Bits b (default)", bits(1, 5, 0), EVERPARSE_ERROR_CONSTRAINT_FAILED);
  check("Bits c", bits(1, 0, 7), 255);
  check("Bits a and c", bits(0, 0, 7), 128);
  check("Bits b and c", bits(3, 7, 7), EVERPARSE_ERROR_CONSTRAINT_FAILED);

  check("Dep ok", dep(2, 42), EVERPARSE_SUCCESS);
  if (dep_out != 42) {
    fprintf(stderr, "FAIL Dep ok: action did not run\n");
    rc = 1;
  }
  check("Dep len 0", dep(0, 42), 202);
  check("Dep len 5", dep(5, 42), 202);
  check("Dep tag (with action)", dep(4, 41), 203);
  if (dep_out != 0) {
    fprintf(stderr, "FAIL Dep tag: action ran on a failing field\n");
    rc = 1;
  }

  check("Paint ok", paint(1), EVERPARSE_SUCCESS);
  check("Paint Blue", paint(3), 211);
  check("Paint not a Color (default)", paint(0), EVERPARSE_ERROR_CONSTRAINT_FAILED);
  check("Paint not a Color (default)", paint(4), EVERPARSE_ERROR_CONSTRAINT_FAILED);

  /* The generated wrappers report the reason of user-defined codes */
  {
    uint8_t buf[3] = { 2, 0, 0 };
    reset();
    if (TestCheckHeader(buf, sizeof(buf)) ||
        wrapper_reason == NULL ||
        strcmp(wrapper_reason, "user-defined constraint failed") != 0) {
      fprintf(stderr, "FAIL TestCheckHeader: expected a user-defined constraint failure\n");
      rc = 1;
    }
  }

  if (rc == 0) {
    printf("error_code test: all checks passed\n");
  }
  return rc;
}
