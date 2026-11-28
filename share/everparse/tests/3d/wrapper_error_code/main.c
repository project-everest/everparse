/* Test driver for --wrapper_error_code. The same driver is linked against
   every variant of the generated code; WRAPPER_ERROR_CODE_RETURN is defined
   for the `return' variants, and the `out' variants are tested otherwise. */

#include "WrapperErrorCodeWrapper.h"

#include <stdio.h>
#include <string.h>
#include <stdbool.h>

/* Filled by the error callback of the wrappers */
static const char *last_reason;

void WrapperErrorCodeEverParseError(const char *StructName,
                                    const char *FieldName,
                                    const char *Reason) {
  (void) StructName;
  (void) FieldName;
  last_reason = Reason;
}

static int rc = 0;

/* Sentinel for "not written by the wrapper" */
#define UNSET 0xeeU

static void expect(const char *name, int ok, int expected_ok,
                   uint8_t code, uint8_t expected_code) {
  if (ok != expected_ok || code != expected_code) {
    fprintf(stderr, "FAIL %s: expected %d with code %u, got %d with code %u\n",
            name, expected_ok, (unsigned) expected_code, ok, (unsigned) code);
    rc = 1;
  } else {
    printf("%s: %s, code %u\n", name, ok ? "accepted" : "rejected", (unsigned) code);
  }
}

static void header(const char *name, uint8_t version, uint8_t kind,
                   uint8_t flags, uint32_t len, int complete,
                   int expected_ok, uint8_t expected_code) {
  uint8_t buf[4] = { version, kind, flags, 0 };
  uint8_t outKind = 0;
  uint8_t code = UNSET;
  BOOLEAN ok;
  last_reason = NULL;
#ifdef WRAPPER_ERROR_CODE_RETURN
  code = complete
    ? WrapperErrorCodeCheckCompleteHeader(&outKind, buf, len)
    : WrapperErrorCodeCheckHeader(&outKind, buf, len);
  ok = code == EVERPARSE_SUCCESS;
#else
  ok = complete
    ? WrapperErrorCodeCheckCompleteHeader(&outKind, buf, len, &code)
    : WrapperErrorCodeCheckHeader(&outKind, buf, len, &code);
#endif
  expect(name, ok ? 1 : 0, expected_ok, code, expected_code);
  if (ok && outKind != kind) {
    fprintf(stderr, "FAIL %s: action did not run\n", name);
    rc = 1;
  }
}

/* Copy buffer and probe functions for the probe wrapper */

typedef struct {
  uint8_t *buf;
  size_t len;
  size_t pos;
} copy_buffer_t;

uint8_t *EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
  return ((copy_buffer_t *) x)->buf;
}

size_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
  return ((copy_buffer_t *) x)->len;
}

size_t *EverParseStreamPos(EVERPARSE_COPY_BUFFER_T x) {
  return &((copy_buffer_t *) x)->pos;
}

static bool init_ok = true;

bool ProbeInit(const char *typename_s, uint64_t len, EVERPARSE_COPY_BUFFER_T dst) {
  (void) typename_s;
  (void) len;
  (void) dst;
  return init_ok;
}

/* The probed address is a pointer to the bytes to validate in place */
bool ProbeInPlace(uint64_t len, uint64_t read_offset, uint64_t write_offset,
                  uint64_t src, EVERPARSE_COPY_BUFFER_T dst) {
  copy_buffer_t *p = dst;
  if (src == 0 || read_offset != 0 || write_offset != 0) {
    return false;
  }
  p->buf = (uint8_t *) (uintptr_t) src;
  p->len = (size_t) len;
  return true;
}

static void probed(const char *name, uint16_t x, uint16_t y,
                   uint64_t providedSize, int null_src,
                   uint32_t expected_result, uint8_t expected_code) {
  uint8_t bytes[4] = {
    (uint8_t) x, (uint8_t) (x >> 8), (uint8_t) y, (uint8_t) (y >> 8)
  };
  copy_buffer_t dest = { NULL, 0, 0 };
#ifdef WRAPPER_ERROR_CODE_RETURN
  /* The validator's error code replaces EVERPARSE_PROBE_FAILURE_VALIDATION */
  uint8_t code = expected_code;
  uint32_t result =
    WrapperErrorCodeProbeInPlaceCheckProbed(
      (EVERPARSE_COPY_BUFFER_T) &dest,
      null_src ? 0 : (uint64_t) (uintptr_t) bytes,
      providedSize);
  if (expected_result == EVERPARSE_PROBE_FAILURE_VALIDATION) {
    expected_result = expected_code;
  }
#else
  uint8_t code = UNSET;
  uint32_t result =
    WrapperErrorCodeProbeInPlaceCheckProbed(
      (EVERPARSE_COPY_BUFFER_T) &dest,
      null_src ? 0 : (uint64_t) (uintptr_t) bytes,
      providedSize,
      &code);
#endif
  if (result != expected_result || code != expected_code) {
    fprintf(stderr, "FAIL %s: expected result %u with code %u, got %u with code %u\n",
            name, (unsigned) expected_result, (unsigned) expected_code,
            (unsigned) result, (unsigned) code);
    rc = 1;
  } else {
    printf("%s: result %u, code %u\n", name, (unsigned) result, (unsigned) code);
  }
}

int main(void) {
  header("Header ok", 1, 3, 0, 3, 0, 1, EVERPARSE_SUCCESS);
  header("Header version", 2, 0, 0, 3, 0, 0, 200);
  header("Header kind (#define)", 1, 4, 0, 3, 0, 0, 201);
  header("Header flags (default)", 1, 0, 1, 3, 0, 0, EVERPARSE_ERROR_CONSTRAINT_FAILED);
  header("Header truncated", 1, 0, 0, 2, 0, 0, EVERPARSE_ERROR_NOT_ENOUGH_DATA);
  /* Trailing bytes: the plain wrapper accepts them, the Complete wrapper
     rejects them although the validator succeeded: the `out' variants
     then store the validator's code (0), while the `return' variants
     return EVERPARSE_ERROR_UNEXPECTED_PADDING */
  header("Header trailing", 1, 0, 0, 4, 0, 1, EVERPARSE_SUCCESS);
  header("Header complete ok", 1, 0, 0, 3, 1, 1, EVERPARSE_SUCCESS);
#ifdef WRAPPER_ERROR_CODE_RETURN
  header("Header complete trailing", 1, 0, 0, 4, 1, 0, EVERPARSE_ERROR_UNEXPECTED_PADDING);
#else
  header("Header complete trailing", 1, 0, 0, 4, 1, 0, EVERPARSE_SUCCESS);
#endif
  if (last_reason == NULL || strcmp(last_reason, "unexpected trailing bytes") != 0) {
    fprintf(stderr, "FAIL Header complete trailing: unexpected reason\n");
    rc = 1;
  }
  header("Header complete kind", 1, 4, 0, 3, 1, 0, 201);

  probed("Probed ok", 1, 2, 4, 0, EVERPARSE_SUCCESS, EVERPARSE_SUCCESS);
  probed("Probed x", 0, 2, 4, 0, EVERPARSE_PROBE_FAILURE_VALIDATION, 210);
  probed("Probed y (default)", 2, 1, 4, 0, EVERPARSE_PROBE_FAILURE_VALIDATION,
         EVERPARSE_ERROR_CONSTRAINT_FAILED);
  /* Failures before validation leave the code at 0 (`out' variants) */
  probed("Probed size", 1, 2, 3, 0, EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE, 0);
  probed("Probed probe", 1, 2, 4, 1, EVERPARSE_PROBE_FAILURE_PROBE, 0);
  init_ok = false;
  probed("Probed init", 1, 2, 4, 0, EVERPARSE_PROBE_FAILURE_INIT, 0);
  init_ok = true;

  if (rc == 0) {
    printf("wrapper_error_code: all checks passed\n");
  }
  return rc;
}
