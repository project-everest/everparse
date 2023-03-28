#ifndef _ExternVector_ExternalTypedefs_H
#define _ExternVector_ExternalTypedefs_H

#include<stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct _POINT {
  uint32_t x;
  uint32_t y;
} POINT;


typedef struct _VEC {
  uint8_t max;
  uint8_t cur;
  POINT   *arr;
} VEC;

#ifdef __cplusplus
}
#endif

#define _ExternVector_ExternalTypedefs_H_DEFINED
#endif
