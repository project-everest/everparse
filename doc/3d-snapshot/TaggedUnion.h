

#ifndef TaggedUnion_H
#define TaggedUnion_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

#define TAGGEDUNION_SIZE8 (8U)

#define TAGGEDUNION_SIZE16 (16U)

#define TAGGEDUNION_SIZE32 (32U)

uint64_t
TaggedUnionValidateInteger(
  uint8_t *Ctxt,
  void
  (*Handler)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

#if defined(__cplusplus)
}
#endif

#define TaggedUnion_H_DEFINED
#endif /* TaggedUnion_H */
