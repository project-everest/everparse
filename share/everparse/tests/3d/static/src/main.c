#include "EverParseStream.h"
#include "TestWrapper.h"
#include <stdio.h>
#include <stdlib.h>

static int failures = 0;

// This function is declared in the generated TestWrapper.c, but not
// defined. It is the callback function called if the validator for
// Test.T fails. Note that for a stream input it is the client's
// EverParseHandleError that the generated wrapper reports through; this one
// is only needed to link. The checks below read the verdict off the wrapper's
// return value, which for a stream input is the number of bytes parsed.
void TestEverParseError(char *StructName, char *FieldName, char *Reason) {
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

#define testSize 18

static void check(int ok, const char *what) {
  printf("%s: %s\n", ok ? "PASS" : "FAIL", what);
  if (!ok)
    ++failures;
}

static void check_ptr(const uint8_t *got, const uint8_t *expected, const uint8_t *origin,
                      const char *what) {
  if (got != expected)
    printf("  expected offset %td, got %td\n", expected - origin, got - origin);
  check(got == expected, what);
}

// Build a stream over a single `len`-byte cell of `buf`, so that the address
// of the byte at stream position p is exactly buf + p. That is what lets the
// field_ptr_after checks below name an expected pointer value.
static EVERPARSE_INPUT_STREAM_BASE single_cell(uint8_t *buf, size_t len) {
  EVERPARSE_INPUT_STREAM_BASE s = EverParseCreate();
  if (s != NULL)
    EverParsePush(s, buf, len);
  return s;
}

// The original test: with three 18-byte cells and a field_ptr_after(18) taken
// 8 bytes in, the 18 requested bytes straddle a cell boundary, so the client
// cannot hand back a contiguous pointer, the action fails, and the validator
// rejects the input without writing through `out`.
static void test_point_not_contiguous(uint8_t *test) {
  uint8_t *out = NULL;
  EVERPARSE_INPUT_STREAM_BASE s = EverParseCreate();
  if (s == NULL) {
    check(0, "POINT: stream allocation");
    return;
  }
  EverParsePush(s, test, (size_t)testSize);
  EverParsePush(s, test, (size_t)testSize);
  EverParsePush(s, test, (size_t)testSize);
  // POINT is 12 bytes; stopping after the 8 that precede the action is how a
  // rejection shows up in the parsed size the wrapper returns.
  check(TestCheckPoint(&out, 0, s) == 8, "POINT: non-contiguous field_ptr_after is rejected");
  check(out == NULL, "POINT: rejected field_ptr_after leaves the output untouched");
  free(s);
}

// Regression test for the *value* written by field_ptr_after. PTRVAL consumes
// 4 + 2 = 6 bytes before the action, which asks for the following 4 bytes, so
// the pointer written must be test + 6. Writing test + 6 + 4 instead -- the
// address past those bytes -- is the bug this guards against: it disagrees
// with Low*, whose action writes the Peep result unchanged, and the F*
// signature of the client primitive leaves the written pointer unconstrained,
// so nothing but this check pins it down.
static void test_field_ptr_after_value(uint8_t *test) {
  uint8_t *out = NULL;
  EVERPARSE_INPUT_STREAM_BASE s = single_cell(test, (size_t)testSize);
  if (s == NULL) {
    check(0, "PTRVAL: stream allocation");
    return;
  }
  check(TestCheckPtrval(&out, 0, s) == 10, "PTRVAL: validation accepted all 10 bytes");
  check_ptr(out, test + 6, test,
            "PTRVAL: field_ptr_after points at the next 4 bytes, not past them");
  free(s);
}

// Same check for the output-type-setter form of the action, which reaches the
// client through field_ptr_after_with_setter but shares the same primitive.
// MIXED consumes 4 + 4 = 8 bytes before the action, so out.p must be test + 8.
static void test_field_ptr_after_setter_value(uint8_t *test) {
  uint32_t seen = 0;
  OPTR out;
  EVERPARSE_INPUT_STREAM_BASE s = single_cell(test, (size_t)testSize);
  if (s == NULL) {
    check(0, "MIXED: stream allocation");
    return;
  }
  out.p = NULL;
  check(TestCheckMixed(&seen, &out, 0, s) == 8, "MIXED: validation accepted all 8 bytes");
  check_ptr(out.p, test + 8, test,
            "MIXED: field_ptr_after setter writes the next 4 bytes, not past them");
  free(s);
}

int main(void) {
  uint8_t *test = calloc(testSize, sizeof(uint8_t));
  if (test == NULL) {
    printf("FAIL: input allocation\n");
    return 1;
  }
  test_point_not_contiguous(test);
  test_field_ptr_after_value(test);
  test_field_ptr_after_setter_value(test);
  free(test);
  if (failures != 0) {
    printf("%d check(s) failed\n", failures);
    return 1;
  }
  printf("All checks passed\n");
  return 0;
}
