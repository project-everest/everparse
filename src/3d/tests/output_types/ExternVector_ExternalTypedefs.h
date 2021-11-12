#ifndef _ExternVector_ExternalTypedefs_H
#define _ExternVector_ExternalTypedefs_H

#include<stdint.h>

typedef struct _Point {
  uint32_t x;
  uint32_t y;
} Point;


typedef struct _Vec {
  uint8_t max;
  uint8_t cur;
  Point   *arr;
} Vec;

#endif
