/* Runtime oracle for field_ptr / field_pos_64 / field_pos_32.

   The grammar in src/Test.3d lays out

     f1 : 10 bytes at offset  0
     f2 :  4 bytes at offset 10
     f3 :  2 bytes at offset 14
     f4 :  4 bytes at offset 16

   and each of f2, f3 and f4 reports its own position through an output
   parameter. The expected values below are the *start* offsets of the annotated
   fields, which is what the Low* backend reports too. Before the fix, each
   action observed the stream position after the field had been consumed, so
   these would have been 14, 16 and base+20 respectively. */

#include <stdio.h>
#include <string.h>
#include "TestWrapper.h"

#define LEN 20

void TestEverParseError(const char *typename,
                        const char *fieldname,
                        const char *reason)
{
  printf("validation failed: %s.%s: %s\n", typename, fieldname, reason);
}

int main(void)
{
  uint8_t buf[LEN];
  uint8_t *out_ptr = NULL;
  uint64_t out_pos64 = 0;
  uint32_t out_pos32 = 0;
  int failed = 0;

  memset(buf, 0, sizeof(buf));

  if (!TestCheckT(&out_ptr, &out_pos64, &out_pos32, buf, LEN))
  {
    printf("FAIL: validation of T failed\n");
    return 1;
  }

  printf("field_pos_64 of f2 = %llu\n", (unsigned long long)out_pos64);
  if (out_pos64 != 10)
  {
    printf("FAIL: expected field_pos_64 of f2 to be 10\n");
    failed = 1;
  }

  printf("field_pos_32 of f3 = %lu\n", (unsigned long)out_pos32);
  if (out_pos32 != 14)
  {
    printf("FAIL: expected field_pos_32 of f3 to be 14\n");
    failed = 1;
  }

  printf("field_ptr of f4 = base + %ld\n", (long)(out_ptr - buf));
  if (out_ptr != buf + 16)
  {
    printf("FAIL: expected field_ptr of f4 to be base + 16\n");
    failed = 1;
  }

  if (failed)
    return 1;

  printf("field_ptr test passed\n");
  return 0;
}
