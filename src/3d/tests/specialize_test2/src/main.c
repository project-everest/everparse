#include "SpecializeVLArrayWrapper.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

typedef struct {
    uint8_t *buf;
    uint64_t len;
} copy_buffer_t;
  
void SpecializeVLArrayEverParseError(char *StructName, char *FieldName, char *Reason) {
    printf("Validation failed in SpecializeVLArray, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

uint8_t * EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
    return ((copy_buffer_t *) x)->buf;
}

uint64_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
    return ((copy_buffer_t *) x)->len;
}

uint64_t UlongToPtr(uint32_t ptr) {
    return (uint64_t) ptr;
}

BOOLEAN ProbeAndCopyLenAux(
    uint64_t bytes_to_read,
    uint64_t read_offset,
    uint64_t write_offset,
    uint8_t *src,
    uint64_t src_len,
    EVERPARSE_COPY_BUFFER_T dst
  )
  {
    copy_buffer_t *p = dst;
    printf("ProbeAndCopyLenAux: bytes_to_read=%lu, read_offset=%lu, write_offset=%lu, src_len=%lu, copy_buffer_len=%lu\n",
        bytes_to_read, read_offset, write_offset, src_len, p->len);
    if (read_offset + bytes_to_read > src_len)
    {
      printf("ProbeAndCopy failed: src_len=%lu, read_offset=%lu, bytes_to_read=%lu\n",
          src_len, read_offset, bytes_to_read);
      return false;
    }
    if (write_offset + bytes_to_read > p->len)
    {
      printf("ProbeAndCopy failed: p->len=%lu, write_offset=%lu, bytes_to_read=%lu\n", 
           p->len, write_offset, bytes_to_read);
      return false;
    }
    memcpy(p->buf + write_offset, src + read_offset, bytes_to_read);
    printf("ProbeAndCopyLenAux succeeded\n");
    return true;
  }
  
BOOLEAN WriteU64(uint64_t src, uint64_t write_offset, EVERPARSE_COPY_BUFFER_T dst)
{
    copy_buffer_t *p = dst;
    if (write_offset + sizeof(uint64_t) > p->len)
    {
        printf("WriteU64 failed\n");
        return false;
    }
    memcpy(p->buf + write_offset, &src, sizeof(uint64_t));
    return true;
}

int UnknownHeaderCount = 4;

typedef struct _UH64 {
  uint16_t NameLength;
  uint16_t RawValueLength;
  uint64_t pName;
  uint64_t pRawValue;
} UH64;

BOOLEAN eq_uh64(UH64 x, UH64 y)
{
  return (
    x.NameLength == y.NameLength &&
    x.RawValueLength == y.RawValueLength &&
    x.pName == y.pName &&
    x.pRawValue == y.pRawValue
  );
}

typedef struct _UH32 {
  uint16_t NameLength;
  uint16_t RawValueLength;
  uint32_t pName;
  uint32_t pRawValue;
} UH32;

BOOLEAN eq_uh32(UH32 x, UH32 y)
{
  return (
    x.NameLength == y.NameLength &&
    x.RawValueLength == y.RawValueLength &&
    x.pName == y.pName &&
    x.pRawValue == y.pRawValue
  );
}
UH64 uh64[4] = {{0,0,0,0},{1,1,1,1},{2,2,2,2},{3,3,3,3}};

UH32 uh32[4] = {{4,4,4,4},{5,5,5,5},{6,6,6,6},{7,7,7,7}};
UH64 uh32_coerced[4] = {{4,4,4,4},{5,5,5,5},{6,6,6,6},{7,7,7,7}};

//Typically, this would be just a raw pointer
//For this test, we simulate a pointer with abstract indexes
BOOLEAN GetSrcPointer(uint64_t src, uint8_t **out, uint64_t *size)
{
  if (src == (uint64_t)uh64)
  {
    *out = (uint8_t*) uh64;
    *size = sizeof(uh64);
  }
  else if (src == (uint64_t)uh32)
  {
    *out = (uint8_t*) uh32;
    *size = sizeof(uh32);
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
  printf("ProbeAndReadU32: read_offset=%lu, src=%lu ...", read_offset, src);
  uint8_t *src_ptr;
  uint64_t src_len;
  uint32_t result = 0;
  if (!GetSrcPointer(src, &src_ptr, &src_len))
  {
    *failed = true;
    printf("GetSrcPointer failed\n");
    return 0;
  }
  printf("src_len=%lu ...", src_len);
  if (read_offset + sizeof(uint32_t) > src_len)
  {
    printf("bounds check failed\n");
    *failed = true;
    return 0;
  }
  printf("ok!\n");
  memcpy(&result, src_ptr + read_offset, sizeof(uint32_t));
  return result;
}

BOOLEAN ProbeAndCopy(
  uint64_t bytes_to_read,
  uint64_t read_offset,
  uint64_t write_offset,
  uint64_t src,
  EVERPARSE_COPY_BUFFER_T dst
)
{
  printf("ProbeAndCopy: bytes_to_read=%ld, read_offset=%ld, write_offset=%ld, src=%ld\n",
      bytes_to_read, read_offset, write_offset, src);
  uint8_t *src_ptr;
  uint64_t src_len;
  if (!GetSrcPointer(src, &src_ptr, &src_len))
  {
    return false;
  }
  return ProbeAndCopyLenAux(bytes_to_read, read_offset, write_offset, src_ptr, src_len, dst);
}

BOOLEAN ProbeInit(uint64_t len, EVERPARSE_COPY_BUFFER_T dst) {
  printf("ProbeInit: len=%lu\n", len);
  copy_buffer_t *cp = (copy_buffer_t*)dst;
  if (len == cp->len)
  { return true; }
  return false;
}

// THE MAIN TEST FUNCTION
int testuh64(void) {
  UH64 dest64[4];
  copy_buffer_t out_64 = (copy_buffer_t) {
    .buf = (uint8_t*)dest64,
    .len = sizeof(dest64)
  };
  uint64_t uh64_ptr = (uint64_t)uh64;
  uint8_t *input_buffer = (uint8_t*)&uh64_ptr;
  printf("Calling validator with pointer %lu, whereas uh64=%lu\n", Load64Le(input_buffer), uh64_ptr);
  if (SpecializeVlarrayCheckUnknownHeaders(
      false,
      UnknownHeaderCount,
      (EVERPARSE_COPY_BUFFER_T) &out_64,
      input_buffer,
      sizeof(uint64_t)
      ))
  {
    if (eq_uh64(uh64[0], dest64[0]) &&
        eq_uh64(uh64[1], dest64[1]) &&
        eq_uh64(uh64[2], dest64[2]) &&
        eq_uh64(uh64[3], dest64[3]))
    {
      printf("Validation succeeded for uh64\n");
      return 0;
    }
    else
    {
      printf("Validation failed for uh64\n");
      return 1;
    }
  }
  return 1;
}

int testuh32(void) {
  UH64 dest64[4];
  copy_buffer_t out_64 = (copy_buffer_t) {
    .buf = (uint8_t*)dest64,
    .len = sizeof(dest64)
  };
  uint64_t uh32_ptr = (uint64_t)uh32;
  uint8_t *input_buffer = (uint8_t*)&uh32_ptr;
  printf("Calling validator with pointer %lu, whereas uh32=%lu\n", Load64Le(input_buffer), uh32_ptr);
  if (SpecializeVlarrayCheckUnknownHeaders(
      true,
      UnknownHeaderCount,
      (EVERPARSE_COPY_BUFFER_T) &out_64,
      input_buffer,
      sizeof(uint64_t)
      ))
  {
    if (eq_uh64(uh32_coerced[0], dest64[0]) &&
        eq_uh64(uh32_coerced[1], dest64[1]) &&
        eq_uh64(uh32_coerced[2], dest64[2]) &&
        eq_uh64(uh32_coerced[3], dest64[3]))
    {
      printf("Validation succeeded for uh32\n");
      return 0;
    }
    else
    {
      printf("Validation failed for uh32\n");
      return 1;
    }
  }
  return 1;
}

int main(void) {
  int result = 0;
  result |= testuh64();
  result |= testuh32();
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