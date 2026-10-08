

#ifndef ReadPair_H
#define ReadPair_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define ReadPair_H_DEFINED
#endif /* ReadPair_H */
