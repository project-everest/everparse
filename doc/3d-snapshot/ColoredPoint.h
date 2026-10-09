

#ifndef ColoredPoint_H
#define ColoredPoint_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
ColoredPointValidateColoredPoint1(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
ColoredPointValidateColoredPoint2(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define ColoredPoint_H_DEFINED
#endif /* ColoredPoint_H */
