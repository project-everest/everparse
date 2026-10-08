

#ifndef Base_H
#define Base_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
BaseValidateUlong(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos,
  size_t *Pos
);

uint8_t
BaseValidatePair(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define Base_H_DEFINED
#endif /* Base_H */
