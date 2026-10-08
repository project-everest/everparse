

#ifndef TaggedUnion_H
#define TaggedUnion_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

#define TAGGEDUNION_SIZE8 (8U)

#define TAGGEDUNION_SIZE16 (16U)

#define TAGGEDUNION_SIZE32 (32U)

uint8_t
TaggedUnionValidateIntPayload(
  uint32_t Size,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
TaggedUnionValidateInteger(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define TaggedUnion_H_DEFINED
#endif /* TaggedUnion_H */
