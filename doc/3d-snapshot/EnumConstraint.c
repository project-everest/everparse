

#include "EnumConstraint.h"

/*
Auto-generated field identifier for error reporting
*/
#define ENUMCONSTRAINT__ENUM_CONSTRAINT__COL ((uint64_t)27U)

/*
Auto-generated field identifier for error reporting
*/
#define ENUMCONSTRAINT__ENUM_CONSTRAINT__X ((uint64_t)28U)

/*
Enum constant
*/
#define RED ((uint32_t)1U)

/*
Enum constant
*/
#define GREEN ((uint32_t)2U)

/*
Enum constant
*/
#define BLUE ((uint32_t)42U)

static inline uint64_t
ValidateEnumConstraintX(
  uint32_t Col,
  uint32_t InputLength,
  uint8_t *Input,
  uint64_t StartPosition
)
/*++
    Internal helper function:
        Validator for field _enum_constraint_x
        of type EnumConstraint._enum_constraint
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterEnumConstraintX;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    positionAfterEnumConstraintX = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterEnumConstraintX = StartPosition + (uint64_t)4U;
  }
  uint64_t endPositionOrError;
  if (EverParseIsError(positionAfterEnumConstraintX))
  {
    endPositionOrError = positionAfterEnumConstraintX;
  }
  else
  {
    /* reading field value */
    uint8_t *base = Input;
    uint32_t enumConstraintX = Load32Le(base + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN
    enumConstraintXConstraintIsOk = enumConstraintX == (uint32_t)(uint8_t)0U || Col == GREEN;
    /* end: checking constraint */
    endPositionOrError =
      EverParseCheckConstraintOk(enumConstraintXConstraintIsOk,
        positionAfterEnumConstraintX);
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      ENUMCONSTRAINT__ENUM_CONSTRAINT__X);
}

uint64_t
EnumConstraintValidateEnumConstraint(
  uint32_t InputLength,
  uint8_t *Input,
  uint64_t StartPosition
)
{
  /* Validating field col */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  uint64_t
  positionAftercol =
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      ENUMCONSTRAINT__ENUM_CONSTRAINT__COL);
  if (EverParseIsError(positionAftercol))
  {
    return positionAftercol;
  }
  uint8_t *base = Input;
  uint32_t col = Load32Le(base + (uint32_t)StartPosition);
  BOOLEAN colConstraintIsOk = col == RED || col == GREEN || col == BLUE;
  uint64_t
  positionOrErrorAftercol =
    EverParseCheckConstraintOkWithFieldId(colConstraintIsOk,
      StartPosition,
      positionAftercol,
      ENUMCONSTRAINT__ENUM_CONSTRAINT__COL);
  if (EverParseIsError(positionOrErrorAftercol))
  {
    return positionOrErrorAftercol;
  }
  /* Field _enum_constraint_x */
  return ValidateEnumConstraintX(col, InputLength, Input, positionOrErrorAftercol);
}

