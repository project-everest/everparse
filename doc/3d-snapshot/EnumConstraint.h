#ifndef __ENUMCONSTRAINT_H
#define __ENUMCONSTRAINT_H

#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "EverParse.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Enum constant */
#define ENUMCONSTRAINT_RED (1U)
/* Enum constant */
#define ENUMCONSTRAINT_GREEN (2U)
/* Enum constant */
#define ENUMCONSTRAINT_BLUE (42U)
uint64_t EnumConstraintValidateEnumConstraint(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start);


#ifdef __cplusplus
}
#endif
#endif

