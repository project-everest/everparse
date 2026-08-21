

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

uint64_t
EnumConstraintValidateEnumConstraint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define EnumConstraint_H_DEFINED
#endif /* EnumConstraint_H */
