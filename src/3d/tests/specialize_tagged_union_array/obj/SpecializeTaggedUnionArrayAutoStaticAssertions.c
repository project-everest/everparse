

#include <stddef.h>
#include <stdint.h>


typedef uint8_t UINT8;
typedef uint16_t UINT16;
typedef uint32_t UINT32;
typedef uint64_t UINT64;
typedef struct _PAYLOAD_0
{
  UINT32 f0;
  UINT64 ptr;
} PAYLOAD_0;

typedef struct ___specialized32__PAYLOAD_0
{
  UINT32 f0;
  UINT32 ptr;
} ___specialized32_PAYLOAD_0;

typedef struct _PAYLOAD_DEFAULT
{
  UINT64 ptr1;
} PAYLOAD_DEFAULT;

typedef struct ___specialized32__PAYLOAD_DEFAULT
{
  UINT32 ptr1;
} ___specialized32_PAYLOAD_DEFAULT;

typedef union _PAYLOAD
{
  PAYLOAD_0 p0_0;
  struct { UINT64 pdef; } __union_case__1;
} PAYLOAD;

typedef union ___specialized32__PAYLOAD
{
  ___specialized32_PAYLOAD_0 p0_0;
  struct { UINT32 pdef; } __union_case__1;
} ___specialized32_PAYLOAD;

typedef struct _WRAPPER
{
  UINT64 Tag;
  PAYLOAD payload;
} WRAPPER;

typedef struct ___specialized32__WRAPPER
{
  UINT64 Tag;
  ___specialized32_PAYLOAD payload;
} ___specialized32_WRAPPER;
#define EVERPARSE_STATIC_ASSERT(e) typedef char __EVERPARSE_STATIC_ASSERT__[(e)?1:-1];
EVERPARSE_STATIC_ASSERT(sizeof(PAYLOAD_0) == 16);
EVERPARSE_STATIC_ASSERT(offsetof(PAYLOAD_0, f0) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(PAYLOAD_0, ptr) == 8);
EVERPARSE_STATIC_ASSERT(sizeof(___specialized32_PAYLOAD_0) == 8);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_PAYLOAD_0, f0) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_PAYLOAD_0, ptr) == 4);
EVERPARSE_STATIC_ASSERT(sizeof(PAYLOAD_DEFAULT) == 8);
EVERPARSE_STATIC_ASSERT(offsetof(PAYLOAD_DEFAULT, ptr1) == 0);
EVERPARSE_STATIC_ASSERT(sizeof(___specialized32_PAYLOAD_DEFAULT) == 4);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_PAYLOAD_DEFAULT, ptr1) == 0);
EVERPARSE_STATIC_ASSERT(sizeof(WRAPPER) == 24);
EVERPARSE_STATIC_ASSERT(offsetof(WRAPPER, Tag) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(WRAPPER, payload) == 8);
EVERPARSE_STATIC_ASSERT(sizeof(___specialized32_WRAPPER) == 16);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_WRAPPER, Tag) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_WRAPPER, payload) == 8);
