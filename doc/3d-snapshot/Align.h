

#ifndef Align_H
#define Align_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
AlignValidateColoredPoint1(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define Align_H_DEFINED
#endif /* Align_H */
