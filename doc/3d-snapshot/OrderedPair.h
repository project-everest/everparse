

#ifndef OrderedPair_H
#define OrderedPair_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
OrderedPairValidateOrderedPair(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define OrderedPair_H_DEFINED
#endif /* OrderedPair_H */
