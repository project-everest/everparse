#include "EverParseStream.h"
#include "TestWrapper.h"
#include <stdio.h>
#include <stdlib.h>

// This function is declared in the generated TestWrapper.c, but not
// defined. It is the callback function called if the validator for
// Test.T fails.
void TestEverParseError(char *StructName, char *FieldName, char *Reason) {
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

#define testSize 18

int main(void) {
  uint8_t *test = calloc(testSize, sizeof(uint8_t));
  uint8_t *out = NULL;
  if (test != NULL) {
    EVERPARSE_INPUT_STREAM_BASE testStream = EverParseCreate();
    if (testStream != NULL) {
      EverParsePush(testStream, test, testSize);
      EverParsePush(testStream, test, testSize);
      EverParsePush(testStream, test, testSize);
      if (TestCheckPoint(&out, 0, testStream)) {
        if (out == NULL) {
          printf("Validation succeeded, but not enough contiguous bytes\n");
        } else {
          printf("Validation succeeded\n");
        }
      }
      free(testStream);
    }
    free(test);
  }
  return 0;
}
