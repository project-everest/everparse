

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
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define TaggedUnion_H_DEFINED
#endif /* TaggedUnion_H */
