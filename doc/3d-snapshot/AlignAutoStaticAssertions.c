

#include <stddef.h>
#include <stdint.h>


typedef uint8_t UINT8;
typedef uint16_t UINT16;
typedef uint32_t UINT32;
typedef uint64_t UINT64;
typedef struct _point
{
  UINT16 x;
  UINT16 y;
} point;

typedef struct _coloredPoint1
{
  UINT8 color;
  point pt;
} coloredPoint1;

typedef struct _coloredPoint2
{
  point pt;
  UINT8 color;
} coloredPoint2;

typedef union _Value
{
  coloredPoint1 cp1_0;
  coloredPoint2 cp2_1;
  struct { point pt;
    UINT16 other; } cp3_2;
} Value;

typedef struct _tlv
{
  UINT8 tag;
  UINT32 length;
  UINT8 other;
} TLV;
#define EVERPARSE_STATIC_ASSERT(e) typedef char __EVERPARSE_STATIC_ASSERT__[(e)?1:-1];
EVERPARSE_STATIC_ASSERT(sizeof(point) == 4);
EVERPARSE_STATIC_ASSERT(offsetof(point, x) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(point, y) == 2);
EVERPARSE_STATIC_ASSERT(sizeof(coloredPoint1) == 6);
EVERPARSE_STATIC_ASSERT(offsetof(coloredPoint1, color) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(coloredPoint1, pt) == 2);
EVERPARSE_STATIC_ASSERT(sizeof(coloredPoint2) == 6);
EVERPARSE_STATIC_ASSERT(offsetof(coloredPoint2, pt) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(coloredPoint2, color) == 4);
EVERPARSE_STATIC_ASSERT(sizeof(TLV) == 10);
EVERPARSE_STATIC_ASSERT(offsetof(TLV, tag) == 0);
EVERPARSE_STATIC_ASSERT(offsetof(TLV, length) == 4);
EVERPARSE_STATIC_ASSERT(offsetof(TLV, other) == 8);
