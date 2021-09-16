

#ifndef __BoundedSum_H
#define __BoundedSum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




uint64_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
);

uint64_t
BoundedSumValidateMySum(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
);

#if defined(__cplusplus)
}
#endif

#define __BoundedSum_H_DEFINED
#endif
