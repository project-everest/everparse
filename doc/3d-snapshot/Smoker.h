

#ifndef __Smoker_H
#define __Smoker_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"


#include "Triangle2.h"

uint64_t
SmokerValidateSmoker(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input
);

#if defined(__cplusplus)
}
#endif

#define __Smoker_H_DEFINED
#endif
