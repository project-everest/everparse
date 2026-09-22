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
  return test_reuse();
}
