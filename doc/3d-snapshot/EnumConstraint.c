

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

static inline uint64_t ValidateEnumConstraintX(uint32_t Col, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _enum_constraint_x
        of type EnumConstraint._enum_constraint
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field x */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition0 = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition0);
  uint64_t resultAfterEnumConstraintX;
  if (hasBytes)
  {
    resultAfterEnumConstraintX = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterEnumConstraintX = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t result;
  if (EverParseIsError(resultAfterEnumConstraintX))
  {
    result = resultAfterEnumConstraintX;
  }
  else
  {
    /* reading field value */
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    memcpy(temp, Input.buf + currentPosition, (uint32_t)4U * sizeof (uint8_t));
    *Input.pos = currentPosition + (uint32_t)4U;
    uint32_t res = Load32Le(temp);
    uint32_t enumConstraintX = res;
    /* start: checking constraint */
    BOOLEAN
    enumConstraintXConstraintIsOk = enumConstraintX == (uint32_t)(uint8_t)0U || Col == GREEN;
    /* end: checking constraint */
    result = EverParseCheckConstraintOk(enumConstraintXConstraintIsOk, resultAfterEnumConstraintX);
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, ENUMCONSTRAINT__ENUM_CONSTRAINT__X);
}

uint64_t EnumConstraintValidateEnumConstraint(EverParseInputBuffer Input)
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  uint32_t startPosition2 = *Input.pos;
  uint64_t startPosition3 = (uint64_t)startPosition2;
  /* Validating field col */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition0 = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition0);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t
  resultAftercol =
    EverParseMaybeSetErrorCode(result,
      startPosition3,
      ENUMCONSTRAINT__ENUM_CONSTRAINT__COL);
  if (EverParseIsError(resultAftercol))
  {
    return resultAftercol;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition = *Input.pos;
  memcpy(temp, Input.buf + currentPosition, (uint32_t)4U * sizeof (uint8_t));
  *Input.pos = currentPosition + (uint32_t)4U;
  uint32_t res = Load32Le(temp);
  uint32_t col = res;
  BOOLEAN colConstraintIsOk = col == RED || col == GREEN || col == BLUE;
  uint64_t
  resultAftercol1 =
    EverParseCheckConstraintOkWithFieldId(colConstraintIsOk,
      startPosition1,
      resultAftercol,
      ENUMCONSTRAINT__ENUM_CONSTRAINT__COL);
  if (EverParseIsError(resultAftercol1))
  {
    return resultAftercol1;
  }
  /* Field _enum_constraint_x */
  return ValidateEnumConstraintX(col, Input);
}

