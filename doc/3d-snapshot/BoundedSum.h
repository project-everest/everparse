

#ifndef BoundedSum_H
#define BoundedSum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
BoundedSumValidateMySum(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define BoundedSum_H_DEFINED
#endif /* BoundedSum_H */
