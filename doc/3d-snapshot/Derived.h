

#ifndef __Derived_H
#define __Derived_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"


#include "Base.h"

uint64_t DerivedValidateTriple(uint32_t Uu, uint8_t *Input, uint64_t StartPosition);

uint64_t DerivedValidateQuad(uint32_t Uu, uint8_t *Input, uint64_t StartPosition);

#if defined(__cplusplus)
}
#endif

#define __Derived_H_DEFINED
#endif
