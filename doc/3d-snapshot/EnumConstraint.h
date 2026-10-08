

#ifndef EnumConstraint_H
#define EnumConstraint_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

/**
Enum constant
*/
#define ENUMCONSTRAINT_RED (1U)

/**
Enum constant
*/
#define ENUMCONSTRAINT_GREEN (2U)

/**
Enum constant
*/
#define ENUMCONSTRAINT_BLUE (42U)

uint8_t
EnumConstraintValidateEnumConstraint(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define EnumConstraint_H_DEFINED
#endif /* EnumConstraint_H */
