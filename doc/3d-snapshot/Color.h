

#ifndef __Color_H
#define __Color_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




/*
Enum constant
*/
#define COLOR_RED ((uint32_t)1U)

/*
Enum constant
*/
#define COLOR_GREEN ((uint32_t)2U)

/*
Enum constant
*/
#define COLOR_BLUE ((uint32_t)42U)

uint64_t
ColorValidateColor(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

typedef uint32_t ColorColor;

uint64_t
ColorValidateColoredPoint(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define __Color_H_DEFINED
#endif
