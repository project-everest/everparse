

#ifndef __BoundedSum_H
#define __BoundedSum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




uint64_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
  uint32_t InputLength,
  uint8_t *Input,
  uint64_t StartPosition
);

uint64_t BoundedSumValidateMySum(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition);

#if defined(__cplusplus)
}
#endif

#define __BoundedSum_H_DEFINED
#endif
