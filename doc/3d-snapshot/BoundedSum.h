

#ifndef __BoundedSum_H
#define __BoundedSum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"


#include "Triangle2.h"

uint64_t BoundedSumValidateBoundedSum(uint32_t Bound, EverParseInputBuffer Input);

uint64_t BoundedSumValidateMySum(EverParseInputBuffer Input);

#if defined(__cplusplus)
}
#endif

#define __BoundedSum_H_DEFINED
#endif
