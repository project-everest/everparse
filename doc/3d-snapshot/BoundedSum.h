

#ifndef BoundedSum_H
#define BoundedSum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

uint64_t
BoundedSumValidateMySum(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

#if defined(__cplusplus)
}
#endif

#define BoundedSum_H_DEFINED
#endif /* BoundedSum_H */
