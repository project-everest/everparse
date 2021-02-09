

#ifndef __TaggedUnion_H
#define __TaggedUnion_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




uint64_t
TaggedUnionValidateInteger(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition);

#if defined(__cplusplus)
}
#endif

#define __TaggedUnion_H_DEFINED
#endif
