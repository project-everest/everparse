

#ifndef ColoredPoint_H
#define ColoredPoint_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
ColoredPointValidateColoredPoint1(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

uint64_t
ColoredPointValidateColoredPoint2(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define ColoredPoint_H_DEFINED
#endif /* ColoredPoint_H */
