

#ifndef Derived_H
#define Derived_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
DerivedValidateTriple(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

uint64_t
DerivedValidateQuad(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define Derived_H_DEFINED
#endif /* Derived_H */
