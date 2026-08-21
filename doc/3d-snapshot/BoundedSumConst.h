

#ifndef BoundedSumConst_H
#define BoundedSumConst_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
BoundedSumConstValidateBoundedSum(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define BoundedSumConst_H_DEFINED
#endif /* BoundedSumConst_H */
