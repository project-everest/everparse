

#ifndef OrderedPair_H
#define OrderedPair_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
OrderedPairValidateOrderedPair(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define OrderedPair_H_DEFINED
#endif /* OrderedPair_H */
