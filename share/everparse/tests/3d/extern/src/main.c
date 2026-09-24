#include "EverParseStream.h"
#include "TestWrapper.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// This function is declared in the generated TestWrapper.c, but not
// defined. It is the callback function called if the validator for
// Test.T fails.
void TestEverParseError(char *StructName, char *FieldName, char *Reason) {
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

#define testSize 18

// Regression test: EverParseStreamGetPosition is cumulative over the life of
// the stream and the shipped EverParseRetreat is a no-op, so a wrapper that
// reported the raw position as the parsed size returned the running total
// rather than the length of the record it had just validated. Validating twice
// on one stream is what exposes it: the second call must report the same size
// as the first.
static int test_reuse(void) {
  uint8_t data[3 * testSize];
  memset(data, 0xFF, sizeof(data)); // so that the `y >= 18` constraint holds
  EVERPARSE_INPUT_STREAM_BASE stream = EverParseCreate();
  if (stream == NULL)
    return 1;
  EverParsePush(stream, data, (size_t)sizeof(data));
  uint64_t first = TestCheckPoint(0, stream);
  uint64_t second = TestCheckPoint(0, stream);
  free(stream);
  printf("Reuse: first = %llu, second = %llu\n", (unsigned long long)first,
         (unsigned long long)second);
  if (first != 12 || second != 12) {
    printf("Reuse: FAILED, expected 12 and 12\n");
    return 1;
  }
  return 0;
}

// Regression test for field positions on a reused extern stream: see the
// comment on FIELDPOS in Test.3d. Both validations must report x at offset 0.
static int test_field_pos(void) {
  uint8_t data[2 * testSize];
  memset(data, 0, sizeof(data));
  EVERPARSE_INPUT_STREAM_BASE stream = EverParseCreate();
  if (stream == NULL)
    return 1;
  EverParsePush(stream, data, (size_t)sizeof(data));
  uint64_t first = 0xFFFF, second = 0xFFFF;
  uint64_t n1 = TestCheckFieldpos(&first, 0, stream);
  uint64_t n2 = TestCheckFieldpos(&second, 0, stream);
  free(stream);
  printf("FieldPos: offsets = %llu %llu, sizes = %llu %llu\n",
         (unsigned long long)first, (unsigned long long)second,
         (unsigned long long)n1, (unsigned long long)n2);
  if (first != 0 || second != 0 || n1 != 8 || n2 != 8) {
    printf("FieldPos: FAILED, expected offsets 0 0 and sizes 8 8\n");
    return 1;
  }
  return 0;
}

// Regression test for truncation on an extern stream: see the comment on EXACT
// in Test.3d. The expected verdicts are those of the buffer backend, on which
// the Low* and Pulse validators are known to agree, for the same bytes and the
// same available length.
typedef uint64_t (*trunc_check)(EVERPARSE_EXTRA_T, EVERPARSE_INPUT_STREAM_BASE);

static int run_trunc(const char *label, trunc_check check, uint8_t len, size_t n,
                     int expected) {
  uint8_t data[6] = {len, 0xAA, 0xBB, 0x99, 0x77, 0x66};
  EVERPARSE_INPUT_STREAM_BASE stream = EverParseCreate();
  if (stream == NULL)
    return 1;
  EverParsePush(stream, data, n);
  EverParseErrorCount = 0;
  check(0, stream);
  free(stream);
  int accepted = (EverParseErrorCount == 0);
  printf("Truncate: %-22s len=%u avail=%u -> %s\n", label, (unsigned)len,
         (unsigned)n, accepted ? "accept" : "reject");
  if (accepted != expected) {
    printf("Truncate: FAILED, expected %s\n", expected ? "accept" : "reject");
    return 1;
  }
  return 0;
}

static int test_truncation(void) {
  int bad = 0;
  bad |= run_trunc("exact/ok", &TestCheckExact, 2, 4, 1);
  bad |= run_trunc("exact/too-long", &TestCheckExact, 3, 4, 0);
  bad |= run_trunc("exact/too-short", &TestCheckExact, 1, 4, 0);
  bad |= run_trunc("exact/empty", &TestCheckExact, 0, 2, 0);
  bad |= run_trunc("exact/two-elements", &TestCheckExact, 4, 6, 0);
  bad |= run_trunc("exact/no-room", &TestCheckExact, 2, 3, 0);
  bad |= run_trunc("atmost/ok", &TestCheckAtmost, 2, 4, 1);
  bad |= run_trunc("atmost/too-long", &TestCheckAtmost, 3, 4, 0);
  bad |= run_trunc("atmost/too-short", &TestCheckAtmost, 1, 4, 0);
  bad |= run_trunc("atmost/empty", &TestCheckAtmost, 0, 2, 0);
  bad |= run_trunc("atmost/slack", &TestCheckAtmost, 4, 6, 1);
  bad |= run_trunc("atmost/no-room", &TestCheckAtmost, 2, 3, 0);
  bad |= run_trunc("nlist/ok", &TestCheckNlist, 2, 4, 1);
  bad |= run_trunc("nlist/odd", &TestCheckNlist, 3, 4, 0);
  bad |= run_trunc("nlist/too-short", &TestCheckNlist, 1, 4, 0);
  bad |= run_trunc("nlist/empty", &TestCheckNlist, 0, 2, 1);
  bad |= run_trunc("nlist/two-elements", &TestCheckNlist, 4, 6, 1);
  bad |= run_trunc("nlist/no-room", &TestCheckNlist, 2, 3, 0);
  return bad;
}

int main(void) {
  uint8_t *test = calloc(testSize, sizeof(uint8_t));
  if (test != NULL) {
    EVERPARSE_INPUT_STREAM_BASE testStream = EverParseCreate();
    if (testStream != NULL) {
      EverParsePush(testStream, test, (size_t)testSize);
      EverParsePush(testStream, test, (size_t)testSize);
      EverParsePush(testStream, test, (size_t)testSize);
      if (TestCheckPoint(0, testStream)) {
        printf("Validation succeeded\n");
      }
      free(testStream);
    }
    free(test);
  }
  return test_reuse() || test_field_pos() || test_truncation();
}
