

#ifndef BF_H
#define BF_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
BfValidateDummy(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

#if defined(__cplusplus)
}
#endif

#define BF_H_DEFINED
#endif /* BF_H */
