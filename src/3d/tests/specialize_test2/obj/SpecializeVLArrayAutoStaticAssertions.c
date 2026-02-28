

#include <stddef.h>
#include <stdint.h>


typedef uint8_t UINT8;
typedef uint16_t UINT16;
typedef uint32_t UINT32;
typedef uint64_t UINT64;
typedef struct _UNKNOWN_HEADER_64
{
  UINT16 NameLength;
  UINT16 RawValueLength;
  UINT64 pName;
  UINT64 pRawValue;
} UNKNOWN_HEADER_64;

typedef struct ___specialized32__UNKNOWN_HEADER_64
{
  UINT16 NameLength;
  UINT16 RawValueLength;
  UINT32 pName;
  UINT32 pRawValue;
} ___specialized32_UNKNOWN_HEADER_64;
#define EVERPARSE_STATIC_ASSERT(e) typedef char __EVERPARSE_STATIC_ASSERT__[(e)?1:-1];
EVERPARSE_STATIC_ASSERT(sizeof(UNKNOWN_HEADER_64) == 24);
EVERPARSE_STATIC_ASSERT(offsetof(UNKNOWN_HEADER_64, NameLength) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(UNKNOWN_HEADER_64, RawValueLength) == 2);
EVERPARSE_STATIC_ASSERT(offsetof(UNKNOWN_HEADER_64, pName) == 8);
EVERPARSE_STATIC_ASSERT(offsetof(UNKNOWN_HEADER_64, pRawValue) == 16);
EVERPARSE_STATIC_ASSERT(sizeof(___specialized32_UNKNOWN_HEADER_64) == 12);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_UNKNOWN_HEADER_64, NameLength) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_UNKNOWN_HEADER_64, RawValueLength) == 2);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_UNKNOWN_HEADER_64, pName) == 4);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_UNKNOWN_HEADER_64, pRawValue) == 8);
