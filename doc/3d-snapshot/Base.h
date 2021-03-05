

#ifndef __Base_H
#define __Base_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




uint64_t BaseValidateUlong(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition);

uint64_t BaseValidatePair(uint32_t Uu, uint8_t *Input, uint64_t StartPosition);

#if defined(__cplusplus)
}
#endif

#define __Base_H_DEFINED
#endif
