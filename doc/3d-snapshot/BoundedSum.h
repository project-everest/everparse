



#ifndef __BoundedSum_H
#define __BoundedSum_H

#include "EverParse.h"
#if defined(__cplusplus)
extern "C" {
#endif

uint64_t
BoundedSumValidateBoundedSum(uint32_t Bound, InputBuffer Input, uint64_t StartPosition);

uint64_t BoundedSumValidateMySum(InputBuffer Input, uint64_t StartPosition);

#if defined(__cplusplus)
}
#endif

#define __BoundedSum_H_DEFINED
#endif
