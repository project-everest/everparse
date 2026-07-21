

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
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define Color_H_DEFINED
#endif /* Color_H */
