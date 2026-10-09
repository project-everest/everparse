

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

uint8_t
ColorValidateColoredPoint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define Color_H_DEFINED
#endif /* Color_H */
