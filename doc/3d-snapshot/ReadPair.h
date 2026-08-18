

#ifndef ReadPair_H
#define ReadPair_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define ReadPair_H_DEFINED
#endif /* ReadPair_H */
