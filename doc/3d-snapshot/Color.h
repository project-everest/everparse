

#ifndef Color_H
#define Color_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

/**
Enum constant
*/
#define COLOR_RED (1U)

/**
Enum constant
*/
#define COLOR_GREEN (2U)

/**
Enum constant
*/
#define COLOR_BLUE (42U)

uint64_t
ColorValidateColoredPoint(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
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

#define Color_H_DEFINED
#endif /* Color_H */
