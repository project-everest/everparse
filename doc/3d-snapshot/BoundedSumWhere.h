

#ifndef BoundedSumWhere_H
#define BoundedSumWhere_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
BoundedSumWhereValidateBoundedSum(
  uint32_t Bound,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define BoundedSumWhere_H_DEFINED
#endif /* BoundedSumWhere_H */
