

#ifndef Derived_H
#define Derived_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
DerivedValidateTriple(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

uint64_t
DerivedValidateQuad(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

#if defined(__cplusplus)
}
#endif

#define Derived_H_DEFINED
#endif /* Derived_H */
