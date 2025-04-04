#include "SpecializeABCWrapper.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include "probecallbacks.h"

typedef struct _A {
  uint32_t a1;
  uint32_t a2;
} A;

typedef struct _B64 {
  uint32_t b1;
  uint64_t pa;
} B64;

typedef struct _B32 {
  uint32_t b1;
  uint32_t pa;
} B32;


A a = {0x00000000, 0x00000001};
B64 b64 = {0x00000000, 0x0000000000000002};
B32 b32 = {0x00000000, 0x00000003};
uint64_t c64 = 0x0000000000000001;
uint64_t c32 = 0x0000000000000004;

B64 b64_null_a = {0x00000000, 0x0000000000000000};
B32 b32_null_a = {0x00000000, 0x00000000};
uint64_t c64_null_a = 0x0000000000000005;
uint64_t c32_null_a = 0x0000000000000006;

//Typically, this would be just a raw pointer
//For this test, we simulate a pointer with abstract indexes
BOOLEAN GetSrcPointer(uint64_t src, uint8_t **out, uint64_t *size)
{
  if (src == UlongToPtr(c64))
  {
    *out = (uint8_t*) &b64;
    *size = sizeof(b64);
  }
  else if (src == UlongToPtr(c32))
  {
    *out = (uint8_t*) &b32;
    *size = sizeof(b32);
  }
  else if (src == UlongToPtr(c64_null_a))
  {
    *out = (uint8_t*) &b64_null_a;
    *size = sizeof(b64_null_a);
  }
  else if (src == UlongToPtr(c32_null_a))
  {
    *out = (uint8_t*) &b32_null_a;
    *size = sizeof(b32_null_a);
  }
  else if (src == UlongToPtr(b64.pa))
  {
    *out = (uint8_t*) &a;
    *size = sizeof(a);
  }
  else if (src == UlongToPtr(b32.pa))
  {
    *out = (uint8_t*) &a;
    *size = sizeof(a);
  }
  else
  {
    return false;
  }
  return true;
}

uint32_t
ProbeAndReadU32(BOOLEAN *failed, uint64_t read_offset, uint64_t src, EVERPARSE_COPY_BUFFER_T x2)
{
  uint8_t *src_ptr;
  uint64_t src_len;
  uint32_t result = 0;
  if (!GetSrcPointer(src, &src_ptr, &src_len))
  {
    *failed = true;
    return 0;
  }
  if (read_offset + sizeof(uint32_t) > src_len)
  {
    *failed = true;
    return 0;
  }
  memcpy(&result, src_ptr + read_offset, sizeof(uint32_t));
  return result;
}

BOOLEAN ProbeAndCopyLen(
  uint64_t bytes_to_read,
  uint64_t read_offset,
  uint64_t write_offset,
  uint64_t src,
  EVERPARSE_COPY_BUFFER_T dst
)
{
  uint8_t *src_ptr;
  uint64_t src_len;
  if (!GetSrcPointer(src, &src_ptr, &src_len))
  {
    return false;
  }
  return ProbeAndCopyLenAux(bytes_to_read, read_offset, write_offset, src_ptr, src_len, dst);
}


BOOLEAN ProbeAndCopy(uint64_t src, uint64_t len, EVERPARSE_COPY_BUFFER_T dst) {
  return ProbeAndCopyLen(len, 0, 0, src, dst);
}

BOOLEAN ProbeInit(uint64_t src, uint64_t len, EVERPARSE_COPY_BUFFER_T dst) {
  return true;
}

// THE MAIN TEST FUNCTION

int test1(void) {
  A destA;
  copy_buffer_t a_out = (copy_buffer_t) {
    .type = COPY_BUFFER_A,
    .buf = (uint8_t*)&destA,
    .len = sizeof(destA)
  };
  B64 destB;
  copy_buffer_t b_out = (copy_buffer_t) {
    .type = COPY_BUFFER_B,
    .buf = (uint8_t*)&destB,
    .len = sizeof(destB)
  };
  if (SpecializeAbcCheckC(
      false, 
      (EVERPARSE_COPY_BUFFER_T) &a_out,
      (EVERPARSE_COPY_BUFFER_T) &b_out,
      (uint8_t*)&c64,
      sizeof(c64)
      ))
  {
    if (destB.b1 == b64.b1 && destB.pa == b64.pa &&
        destA.a1 == a.a1 && destA.a2 == a.a2)
    {
      printf("Validation succeeded for c64:\nb.b1=%d, b.pa=%ld\na.a1=%d, a.a2=%d\n",
          destB.b1, destB.pa,
          destA.a1, destA.a2
          );
    }
    else
    {
      printf("Validation failed for c64\n");
      return 1;
    }
  }
  else
  {
    printf("Validation failed for c64\n");
    return 1;
  }
  if (SpecializeAbcCheckC(
    true, 
    (EVERPARSE_COPY_BUFFER_T) &a_out,
    (EVERPARSE_COPY_BUFFER_T) &b_out,
    (uint8_t*)&c32,
    sizeof(c32)
    ))
  {
    if (destB.b1 == b32.b1 && destB.pa == UlongToPtr(b32.pa) &&
        destA.a1 == a.a1 && destA.a2 == a.a2)
    {
      printf("Validation succeeded for c32:\nb.b1=%d, b.pa=%ld\na.a1=%d, a.a2=%d\n",
          destB.b1, destB.pa,
          destA.a1, destA.a2
          );
    }
    else
    {
      printf("Validation failed for c32\n");
      return 1;
    }
  } 
  else
  {
    printf("Validation failed for c32\n");
    return 1;
  }
  return 0;
}

int test2(void) {
  A destA = {0x00000000, 0x00000000};
  copy_buffer_t a_out = (copy_buffer_t) {
    .type = COPY_BUFFER_A,
    .buf = (uint8_t*)&destA,
    .len = sizeof(destA)
  };
  B64 destB;
  copy_buffer_t b_out = (copy_buffer_t) {
    .type = COPY_BUFFER_B,
    .buf = (uint8_t*)&destB,
    .len = sizeof(destB)
  };
  if (SpecializeAbcCheckC(
      false, 
      (EVERPARSE_COPY_BUFFER_T) &a_out,
      (EVERPARSE_COPY_BUFFER_T) &b_out,
      (uint8_t*)&c64_null_a,
      sizeof(c64_null_a)
      ))
  {
    if (destB.b1 == b64_null_a.b1 && destB.pa == b64_null_a.pa &&
        destA.a1 == 0 && destA.a2 == 0)
    {
      printf("Validation succeeded for c64_null_a:\nb.b1=%d, b.pa=%ld\na.a1=%d, a.a2=%d\n",
          destB.b1, destB.pa,
          destA.a1, destA.a2
          );
    }
    else
    {
      printf("Validation failed for c64_null_a:\nb.b1=%d, b.pa=%ld\na.a1=%d, a.a2=%d\n",
        destB.b1, destB.pa,
        destA.a1, destA.a2
        );
      return 1;
    }
  }
  else
  {
    printf("Validation failed for c64_null_a (validator failed)\n");
    return 1;
  }
  if (SpecializeAbcCheckC(
    true, 
    (EVERPARSE_COPY_BUFFER_T) &a_out,
    (EVERPARSE_COPY_BUFFER_T) &b_out,
    (uint8_t*)&c32_null_a,
    sizeof(c32_null_a)
    ))
  {
    if (destB.b1 == b32_null_a.b1 && destB.pa == UlongToPtr(b32_null_a.pa) &&
        destA.a1 == 0 && destA.a2 == 0)
    {
      printf("Validation succeeded for c32_null_a:\nb.b1=%d, b.pa=%ld\na.a1=%d, a.a2=%d\n",
          destB.b1, destB.pa,
          destA.a1, destA.a2
          );
    }
    else
    {
      printf("Validation failed for c32_null_a:\nb.b1=%d, b.pa=%ld\na.a1=%d, a.a2=%d\n",
        destB.b1, destB.pa,
        destA.a1, destA.a2
        );
      return 1;
    }
  } 
  else
  {
    printf("Validation failed for c32_null_a\n");
    return 1;
  }
  return 0;
}

int main(void) {
  int result = test1();
  result |= test2();
  if (result == 0)
  {
    printf("All tests passed\n");
  }
  else
  {
    printf("Some tests failed\n");
  }
  return result;
}