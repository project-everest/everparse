

#ifndef __Derived_H
#define __Derived_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"


#include "Base.h"

uint64_t
DerivedValidateTriple(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
);

uint64_t
DerivedValidateQuad(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
);

#if defined(__cplusplus)
}
#endif

#define __Derived_H_DEFINED
#endif
