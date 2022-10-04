

#ifndef __EnumConstraint_H
#define __EnumConstraint_H

#if defined(__cplusplus)
extern "C" {
#endif





#include "EverParse.h"
/*
Enum constant
*/
#define ENUMCONSTRAINT_RED ((uint32_t)1U)

/*
Enum constant
*/
#define ENUMCONSTRAINT_GREEN ((uint32_t)2U)

/*
Enum constant
*/
#define ENUMCONSTRAINT_BLUE ((uint32_t)42U)

uint64_t
EnumConstraintValidateEnumConstraint(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define __EnumConstraint_H_DEFINED
#endif
