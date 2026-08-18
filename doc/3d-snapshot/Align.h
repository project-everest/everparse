

#ifndef Align_H
#define Align_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
AlignValidateColoredPoint1(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define Align_H_DEFINED
#endif /* Align_H */
