

#ifndef __TaggedUnion_H
#define __TaggedUnion_H

#if defined(__cplusplus)
extern "C" {
#endif





#include "EverParse.h"
#define TAGGEDUNION_SIZE8 ((uint8_t)8U)

#define TAGGEDUNION_SIZE16 ((uint8_t)16U)

#define TAGGEDUNION_SIZE32 ((uint8_t)32U)

uint64_t
TaggedUnionValidateInteger(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define __TaggedUnion_H_DEFINED
#endif
