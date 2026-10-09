

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
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

#if defined(__cplusplus)
}
#endif

#define ReadPair_H_DEFINED
#endif /* ReadPair_H */
