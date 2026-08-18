#include <stdint.h>
typedef struct _point {
  uint16_t x;
  uint16_t y;
} point;

typedef struct _coloredPoint1 {
  uint8_t color;
  point pt;
} coloredPoint1;

typedef struct _coloredPoint2 {
  point pt;
  uint8_t color;
} coloredPoint2;

typedef union _Value {
  coloredPoint1 cp1;
  coloredPoint2 cp2;
  struct {
    point pt;
    uint16_t other;
  } cp3;
} Value;

typedef struct _tlv {
  uint8_t tag;
  uint32_t length;
  uint8_t other;
  Value payload[0];
} TLV;