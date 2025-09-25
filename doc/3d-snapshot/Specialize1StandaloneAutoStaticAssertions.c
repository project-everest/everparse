

#include <stddef.h>
#include <stdint.h>


typedef uint8_t UINT8;
typedef uint16_t UINT16;
typedef uint32_t UINT32;
typedef uint64_t UINT64;
typedef struct _T
{
  UINT32 t1;
  UINT32 t2;
} T;

typedef struct ___specialized32__T
{
  UINT32 t1;
  UINT32 t2;
} ___specialized32_T;

typedef struct _S64
{
  UINT32 s1;
  UINT64 ptrT;
  UINT32 s2;
} S64;

typedef struct ___specialized32__S64
{
  UINT32 s1;
  UINT32 ptrT;
  UINT32 s2;
} ___specialized32_S64;

typedef struct _R64
{
  UINT32 r1;
  UINT64 ptrS;
} R64;

typedef struct ___specialized_R32
{
  UINT32 r1;
  UINT32 ptrS;
} R32;
#define EVERPARSE_STATIC_ASSERT(e) typedef char __EVERPARSE_STATIC_ASSERT__[(e)?1:-1];
EVERPARSE_STATIC_ASSERT(sizeof(T) == 8);
EVERPARSE_STATIC_ASSERT(offsetof(T, t1) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(T, t2) == 4);
EVERPARSE_STATIC_ASSERT(sizeof(___specialized32_T) == 8);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_T, t1) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_T, t2) == 4);
EVERPARSE_STATIC_ASSERT(sizeof(S64) == 24);
EVERPARSE_STATIC_ASSERT(offsetof(S64, s1) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(S64, ptrT) == 8);
EVERPARSE_STATIC_ASSERT(offsetof(S64, s2) == 16);
EVERPARSE_STATIC_ASSERT(sizeof(___specialized32_S64) == 12);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_S64, s1) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_S64, ptrT) == 4);
EVERPARSE_STATIC_ASSERT(offsetof(___specialized32_S64, s2) == 8);
EVERPARSE_STATIC_ASSERT(sizeof(R64) == 16);
EVERPARSE_STATIC_ASSERT(offsetof(R64, r1) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(R64, ptrS) == 8);
EVERPARSE_STATIC_ASSERT(sizeof(R32) == 8);
EVERPARSE_STATIC_ASSERT(offsetof(R32, r1) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(R32, ptrS) == 4);
