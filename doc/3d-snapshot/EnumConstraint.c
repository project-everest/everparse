

#include "EnumConstraint.h"

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
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _enum_constraint_x
        of type EnumConstraint._enum_constraint
--*/
{
  /* Validating field x */
  uint32_t positionBeforeEnumConstraint = *Input.pos;
  uint32_t positionBeforeEnumConstraint1 = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterEnumConstraint;
  if (hasBytes)
  {
    resultAfterEnumConstraint = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterEnumConstraint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t resultAfterEnumConstraint0;
  if (EverParseIsSuccess(resultAfterEnumConstraint))
  {
    resultAfterEnumConstraint0 = resultAfterEnumConstraint;
  }
  else
  {
    Err("_enum_constraint",
      "_enum_constraint_x",
      EverParseErrorReasonOfResult(resultAfterEnumConstraint),
      Ctxt,
      Input,
      positionBeforeEnumConstraint1);
    resultAfterEnumConstraint0 = resultAfterEnumConstraint;
  }
  uint64_t resultAfterEnumConstraint1;
  if (EverParseIsError(resultAfterEnumConstraint0))
  {
    resultAfterEnumConstraint1 = resultAfterEnumConstraint0;
  }
  else
  {
    /* reading field value */
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    uint8_t *res = Input.buf + currentPosition;
    *Input.pos = currentPosition + (uint32_t)4U;
    uint8_t *temp1 = res;
    uint32_t res0 = Load32Le(temp1);
    uint32_t enumConstraint1 = res0;
    /* start: checking constraint */
    BOOLEAN
    enumConstraintConstraintIsOk = enumConstraint1 == (uint32_t)(uint8_t)0U || Col == GREEN;
    /* end: checking constraint */
    resultAfterEnumConstraint1 =
      EverParseCheckConstraintOk(enumConstraintConstraintIsOk,
        resultAfterEnumConstraint0);
  }
  if (EverParseIsSuccess(resultAfterEnumConstraint1))
  {
    return resultAfterEnumConstraint1;
  }
  Err("_enum_constraint",
    "_enum_constraint_x.refinement",
    EverParseErrorReasonOfResult(resultAfterEnumConstraint1),
    Ctxt,
    Input,
    positionBeforeEnumConstraint);
  return resultAfterEnumConstraint1;
}

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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field col */
  uint32_t positionBeforeEnumConstraint = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterEnumConstraint;
  if (hasBytes)
  {
    resultAfterEnumConstraint = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterEnumConstraint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t resultAftercol;
  if (EverParseIsSuccess(resultAfterEnumConstraint))
  {
    resultAftercol = resultAfterEnumConstraint;
  }
  else
  {
    Err("_enum_constraint",
      "col",
      EverParseErrorReasonOfResult(resultAfterEnumConstraint),
      Ctxt,
      Input,
      positionBeforeEnumConstraint);
    resultAftercol = resultAfterEnumConstraint;
  }
  if (EverParseIsError(resultAftercol))
  {
    return resultAftercol;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition0 = *Input.pos;
  uint8_t *res = Input.buf + currentPosition0;
  *Input.pos = currentPosition0 + (uint32_t)4U;
  uint8_t *temp1 = res;
  uint32_t res0 = Load32Le(temp1);
  uint32_t col = res0;
  BOOLEAN colConstraintIsOk = col == RED || col == GREEN || col == BLUE;
  uint64_t
  resultAftercol1 =
    EverParseCheckConstraintOkWithFieldId(colConstraintIsOk,
      startPosition1,
      resultAftercol,
      (uint64_t)1U);
  if (EverParseIsError(resultAftercol1))
  {
    return resultAftercol1;
  }
  /* Field _enum_constraint_x */
  uint32_t positionBeforeEnumConstraint0 = *Input.pos;
  uint64_t resultAfterEnumConstraint0 = ValidateEnumConstraintX(col, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterEnumConstraint0))
  {
    return resultAfterEnumConstraint0;
  }
  Err("_enum_constraint",
    "x",
    EverParseErrorReasonOfResult(resultAfterEnumConstraint0),
    Ctxt,
    Input,
    positionBeforeEnumConstraint0);
  return resultAfterEnumConstraint0;
}

