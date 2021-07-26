

#ifndef __Base_H
#define __Base_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"


#include "Triangle2.h"

uint64_t BaseValidateUlong(EverParseInputBuffer Sl);

uint64_t BaseValidatePair(EverParseInputBuffer Input);

#if defined(__cplusplus)
}
#endif

#define __Base_H_DEFINED
#endif
