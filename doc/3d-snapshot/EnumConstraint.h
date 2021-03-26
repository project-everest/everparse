

#ifndef __EnumConstraint_H
#define __EnumConstraint_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




uint64_t
EnumConstraintValidateEnumConstraint(
  uint32_t InputLength,
  uint8_t *Input,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define __EnumConstraint_H_DEFINED
#endif
