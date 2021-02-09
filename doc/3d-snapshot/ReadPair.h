

#ifndef __ReadPair_H
#define __ReadPair_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




uint64_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
  uint32_t Uu,
  uint8_t *Input,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define __ReadPair_H_DEFINED
#endif
