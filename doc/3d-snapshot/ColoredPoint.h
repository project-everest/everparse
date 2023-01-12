

#ifndef __ColoredPoint_H
#define __ColoredPoint_H

#if defined(__cplusplus)
extern "C" {
#endif





#include "EverParse.h"
uint64_t
ColoredPointValidateColoredPoint1(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

uint64_t
ColoredPointValidateColoredPoint2(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define __ColoredPoint_H_DEFINED
#endif
