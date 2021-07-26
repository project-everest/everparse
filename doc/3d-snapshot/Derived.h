

#ifndef __Derived_H
#define __Derived_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"


#include "Base.h"
#include "Triangle2.h"

uint64_t DerivedValidateTriple(EverParseInputBuffer Input);

uint64_t DerivedValidateQuad(EverParseInputBuffer Input);

#if defined(__cplusplus)
}
#endif

#define __Derived_H_DEFINED
#endif
