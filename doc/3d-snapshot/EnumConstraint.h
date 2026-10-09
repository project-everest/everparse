

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
EnumConstraintValidateCoreEnumConstraint(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint64_t
EnumConstraintValidateEnumConstraint(
  uint8_t *Ctxt,
  void
  (*Handler)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

#if defined(__cplusplus)
}
#endif

#define EnumConstraint_H_DEFINED
#endif /* EnumConstraint_H */
