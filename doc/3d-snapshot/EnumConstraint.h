

#ifndef __EnumConstraint_H
#define __EnumConstraint_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




uint64_t
EnumConstraintValidateEnumConstraint(
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
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define __EnumConstraint_H_DEFINED
#endif
