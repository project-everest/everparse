

#ifndef GetFieldPtr_H
#define GetFieldPtr_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
GetFieldPtrValidateT(
  uint8_t **Out,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
GetFieldPtrValidateTact(
  uint8_t **Out,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define GetFieldPtr_H_DEFINED
#endif /* GetFieldPtr_H */
