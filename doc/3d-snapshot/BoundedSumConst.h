

#ifndef BoundedSumConst_H
#define BoundedSumConst_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
BoundedSumConstValidateBoundedSum(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

#if defined(__cplusplus)
}
#endif

#define BoundedSumConst_H_DEFINED
#endif /* BoundedSumConst_H */
