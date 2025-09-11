#include "SpecializeTaggedUnionArrayWrapper.h"
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

typedef struct {
    uint8_t *buf;
    uint64_t len;
} copy_buffer_t;
  
void SpecializeTaggedUnionArrayEverParseError(char *StructName, char *FieldName, char *Reason) {
    printf("Validation failed in SpecializeTaggedUnionArray, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
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



typedef struct _PAYLOAD_0_64 {
  uint32_t f0;
  uint64_t ptr;
} PAYLOAD_0_64;

typedef struct _PAYLOAD_DEFAULT_64 {
  uint64_t ptr1;
} PAYLOAD_DEFAULT_64;

typedef union _PAYLOAD_64 {
  PAYLOAD_0_64 p0;
  PAYLOAD_DEFAULT_64 p;
} PAYLOAD_64;

typedef struct _WRAPPER_64 {
  uint64_t Tag;
  PAYLOAD_64 payload;
} WRAPPER_64;

WRAPPER_64 w64_array[4] = { 
{0 , {.p0={0, 1}}},
{17, {.p={42}}},
{0 , {.p0={2, 3}}},
{.Tag=84, {.p={168}}}
};


WRAPPER_64 w64_array_bad[4] = { 
{0 , {.p0={0, 1}}},
{0, {.p={42}}},
{0 , {.p0={2, 3}}},
{.Tag=0, {.p={168}}}
};
  
typedef struct _PAYLOAD_0_32 {
  uint32_t f0;
  uint32_t ptr;
} PAYLOAD_0_32;

typedef struct _PAYLOAD_DEFAULT_32 {
  uint32_t ptr1;
} PAYLOAD_DEFAULT_32;

typedef union _PAYLOAD_32 {
  PAYLOAD_0_32 p0;
  PAYLOAD_DEFAULT_32 p;
} PAYLOAD_32;

typedef struct _WRAPPER_32 {
  uint64_t Tag;
  PAYLOAD_32 payload;
} WRAPPER_32;

WRAPPER_32 w32_array[4] = { 
{0 , {.p0={4, 5}}},
{13, {.p={26}}},
{0 , {.p0={6, 7}}},
{.Tag=3141, {.p={59}}}
};

WRAPPER_64 w32_array_coerced[4] = { 
{0 , {.p0={4, 5}}},
{13, {.p={26}}},
{0 , {.p0={6, 7}}},
{.Tag=3141, {.p={59}}}
};


WRAPPER_32 w32_array_bad[4] = { 
{0 , {.p0={4, 5}}},
{0, {.p={26}}},
{0 , {.p0={6, 7}}},
{.Tag=0, {.p={59}}}
};

BOOLEAN eq_payload_0_64(PAYLOAD_0_64 x, PAYLOAD_0_64 y)
{
  return (
    x.f0 == y.f0 &&
    x.ptr == y.ptr
  );
}

BOOLEAN eq_wrapper64(WRAPPER_64 x, WRAPPER_64 y)
{
  if (x.Tag == y.Tag) {
    if (x.Tag == 0) {
      return eq_payload_0_64(x.payload.p0, y.payload.p0);
    }
    else {
      return x.payload.p.ptr1 == y.payload.p.ptr1;
    }
  }
  return false;
}

BOOLEAN eq_payload_0_32(PAYLOAD_0_32 x, PAYLOAD_0_32 y)
{
  return (
    x.f0 == y.f0 &&
    x.ptr == y.ptr
  );
}

BOOLEAN eq_wrapper32(WRAPPER_32 x, WRAPPER_32 y)
{
  if (x.Tag == y.Tag) {
    if (x.Tag == 0) {
      return eq_payload_0_32(x.payload.p0, y.payload.p0);
    }
    else {
      return x.payload.p.ptr1 == y.payload.p.ptr1;
    }
  }
  return false;
}


//Typically, this would be just a raw pointer
//For this test, we simulate a pointer with abstract indexes
BOOLEAN GetSrcPointer(uint64_t src, uint8_t **out, uint64_t *size)
{
  if (src == (uint64_t)w64_array)
  {
    *out = (uint8_t*) w64_array;
    *size = sizeof(w64_array);
  }
  else if (src == (uint64_t)w32_array)
  {
    *out = (uint8_t*) w32_array;
    *size = sizeof(w32_array);
  }
  else if (src == (uint64_t)w32_array_bad)
  {
    *out = (uint8_t*) w32_array_bad;
    *size = sizeof(w32_array_bad);
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

uint32_t
ProbeAndReadU64(BOOLEAN *failed, uint64_t read_offset, uint64_t src, EVERPARSE_COPY_BUFFER_T x2)
{
  printf("ProbeAndReadU32: read_offset=%lu, src=%lu ...", read_offset, src);
  uint8_t *src_ptr;
  uint64_t src_len;
  uint64_t result = 0;
  if (!GetSrcPointer(src, &src_ptr, &src_len))
  {
    *failed = true;
    printf("GetSrcPointer failed\n");
    return 0;
  }
  printf("src_len=%lu ...", src_len);
  if (read_offset + sizeof(uint64_t) > src_len)
  {
    printf("bounds check failed\n");
    *failed = true;
    return 0;
  }
  printf("ok!\n");
  memcpy(&result, src_ptr + read_offset, sizeof(uint64_t));
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
  WRAPPER_64 dest64[4];
  copy_buffer_t out_64 = (copy_buffer_t) {
    .buf = (uint8_t*)dest64,
    .len = sizeof(dest64)
  };
  uint64_t wrapper_64_ptr = (uint64_t)w64_array;
  uint8_t *input_buffer = (uint8_t*)&wrapper_64_ptr;
  printf("Calling validator with pointer %lu, whereas wrapper_64=%lu\n", Load64Le(input_buffer), wrapper_64_ptr);
  if (SpecializeTaggedUnionArrayCheckMain(
      false,
      4,
      (EVERPARSE_COPY_BUFFER_T) &out_64,
      input_buffer,
      sizeof(uint64_t)
      ))
  {
    if (eq_wrapper64(w64_array[0], dest64[0]) &&
        eq_wrapper64(w64_array[1], dest64[1]) &&
        eq_wrapper64(w64_array[2], dest64[2]) &&
        eq_wrapper64(w64_array[3], dest64[3]))
    {
      printf("Validation succeeded for 64-bit array\n");
      return 0;
    }
    else
    {
      printf("Validation failed for 64-bit array\n");
      return 1;
    }
  }
  return 1;
}

int testuh32(void) {
  WRAPPER_64 dest64[4];
  copy_buffer_t out_64 = (copy_buffer_t) {
    .buf = (uint8_t*)dest64,
    .len = sizeof(dest64)
  };
  uint64_t w32_ptr = (uint64_t)w32_array;
  uint8_t *input_buffer = (uint8_t*)&w32_ptr;
  printf("Calling validator with pointer %lu, whereas w32=%lu\n", Load64Le(input_buffer), w32_ptr);
  if (SpecializeTaggedUnionArrayCheckMain(
      true,
      4,
      (EVERPARSE_COPY_BUFFER_T) &out_64,
      input_buffer,
      sizeof(uint64_t)
      ))
  {
    if (eq_wrapper64(w32_array_coerced[0], dest64[0]) &&
        eq_wrapper64(w32_array_coerced[1], dest64[1]) &&
        eq_wrapper64(w32_array_coerced[2], dest64[2]) &&
        eq_wrapper64(w32_array_coerced[3], dest64[3]))
    {
      printf("Validation succeeded for 32-bit array\n");
      return 0;
    }
    else
    {
      printf("Validation failed for 32-bit array\n");
      return 1;
    }
  }
  return 1;
}


int testuh64_bad(void) {
  WRAPPER_64 dest64[4];
  copy_buffer_t out_64 = (copy_buffer_t) {
    .buf = (uint8_t*)dest64,
    .len = sizeof(dest64)
  };
  uint64_t w64_ptr = (uint64_t)w64_array_bad;
  uint8_t *input_buffer = (uint8_t*)&w64_ptr;
  printf("Calling validator with pointer %lu, whereas w64=%lu\n", Load64Le(input_buffer), w64_ptr);
  if (SpecializeTaggedUnionArrayCheckMain(
      true,
      4,
      (EVERPARSE_COPY_BUFFER_T) &out_64,
      input_buffer,
      sizeof(uint64_t)
      ))
  {
    printf("Validation succeeded for 64-bit array, when it should have failed\n");
    return 1;
  }
  return 0;
}


int testuh32_bad(void) {
  WRAPPER_64 dest64[4];
  copy_buffer_t out_64 = (copy_buffer_t) {
    .buf = (uint8_t*)dest64,
    .len = sizeof(dest64)
  };
  uint64_t w32_ptr = (uint64_t)w32_array_bad;
  uint8_t *input_buffer = (uint8_t*)&w32_ptr;
  printf("Calling validator with pointer %lu, whereas w32=%lu\n", Load64Le(input_buffer), w32_ptr);
  if (SpecializeTaggedUnionArrayCheckMain(
      true,
      4,
      (EVERPARSE_COPY_BUFFER_T) &out_64,
      input_buffer,
      sizeof(uint64_t)
      ))
  {
    printf("Validation succeeded for 32-bit array, when it should have failed\n");
    return 1;
  }
  return 0;
}

int main(void) {
  int result = 0;
  result |= testuh64();
  result |= testuh32();
  result |= testuh64_bad();
  result |= testuh32_bad();
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