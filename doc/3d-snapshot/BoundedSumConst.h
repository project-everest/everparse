

#ifndef __BoundedSumConst_H
#define __BoundedSumConst_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




/*
 The following will fail because of integer overflow
// SNIPPET_START: boundedSumNaive
entrypoint typedef struct _boundedSum {
  UINT32 left;
  UINT32 right { left + right <= 42 };
} boundedSum;
// SNIPPET_END: boundedSumNaive

*/
uint64_t
BoundedSumConstValidateBoundedSum(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition);

#if defined(__cplusplus)
}
#endif

#define __BoundedSumConst_H_DEFINED
#endif
