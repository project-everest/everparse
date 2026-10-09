

#ifndef Derived_H
#define Derived_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
DerivedValidateTriple(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
DerivedValidateQuad(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define Derived_H_DEFINED
#endif /* Derived_H */
