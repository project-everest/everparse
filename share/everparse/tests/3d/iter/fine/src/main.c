#include "TestWrapper.h"
#include <stdio.h>
#include <stdlib.h>

// This function is declared in the generated TestWrapper.c, but not
// defined. It is the callback function called if the validator for
// Test.T fails.
void TestEverParseError(char *StructName, char *FieldName, char *Reason) {
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

// Example

#define testSize 42 // total input byte size
#define inSize 32 // input pair array byte size
#define outCount 3 // output pair array element count 

int main(void) {
  uint8_t test[testSize];
  OUT_PAIR array[outCount]; // output only, no need to initialize
  OUT_T out = {
    .current = array,
    .remainingCount = outCount
  };
  * (uint32_t*) test = 0;
  test[0] = inSize;
  if (TestCheckContainer(&out, test, testSize))
    printf("Validation succeeded\n");
  else
    printf("Validation failed\n");
  return 0;
}
