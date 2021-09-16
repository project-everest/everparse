

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
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _enum_constraint_x
        of type EnumConstraint._enum_constraint
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterEnumConstraint;
  if (hasBytes)
  {
    positionAfterEnumConstraint = Pos + (uint64_t)4U;
  }
  else
  {
    positionAfterEnumConstraint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  uint64_t positionAfterEnumConstraint0;
  if (EverParseIsSuccess(positionAfterEnumConstraint))
  {
    positionAfterEnumConstraint0 = positionAfterEnumConstraint;
  }
  else
  {
    Err("_enum_constraint",
      "_enum_constraint_x",
      EverParseErrorReasonOfResult(positionAfterEnumConstraint),
      Ctxt,
      Input,
      Pos);
    positionAfterEnumConstraint0 = positionAfterEnumConstraint;
  }
  uint64_t positionAfterEnumConstraint1;
  if (EverParseIsError(positionAfterEnumConstraint0))
  {
    positionAfterEnumConstraint1 = positionAfterEnumConstraint0;
  }
  else
  {
    /* reading field value */
    uint8_t temp[4U] = { 0U };
    uint8_t *temp1 = Input.buf + (uint32_t)Pos;
    uint32_t res = Load32Le(temp1);
    uint32_t enumConstraint1 = res;
    /* start: checking constraint */
    BOOLEAN
    enumConstraintConstraintIsOk = enumConstraint1 == (uint32_t)(uint8_t)0U || Col == GREEN;
    /* end: checking constraint */
    positionAfterEnumConstraint1 =
      EverParseCheckConstraintOk(enumConstraintConstraintIsOk,
        positionAfterEnumConstraint0);
  }
  if (EverParseIsSuccess(positionAfterEnumConstraint1))
  {
    return positionAfterEnumConstraint1;
  }
  Err("_enum_constraint",
    "_enum_constraint_x.refinement",
    EverParseErrorReasonOfResult(positionAfterEnumConstraint1),
    Ctxt,
    Input,
    Pos);
  return positionAfterEnumConstraint1;
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
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t StartPosition
)
{
  /* Validating field col */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= ((uint64_t)Input.len - StartPosition);
  uint64_t positionAfterEnumConstraint;
  if (hasBytes)
  {
    positionAfterEnumConstraint = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterEnumConstraint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAftercol;
  if (EverParseIsSuccess(positionAfterEnumConstraint))
  {
    positionAftercol = positionAfterEnumConstraint;
  }
  else
  {
    Err("_enum_constraint",
      "col",
      EverParseErrorReasonOfResult(positionAfterEnumConstraint),
      Ctxt,
      Input,
      StartPosition);
    positionAftercol = positionAfterEnumConstraint;
  }
  if (EverParseIsError(positionAftercol))
  {
    return positionAftercol;
  }
  uint8_t temp[4U] = { 0U };
  uint8_t *temp1 = Input.buf + (uint32_t)StartPosition;
  uint32_t res = Load32Le(temp1);
  uint32_t col = res;
  BOOLEAN colConstraintIsOk = col == RED || col == GREEN || col == BLUE;
  uint64_t positionAftercol1 = EverParseCheckConstraintOk(colConstraintIsOk, positionAftercol);
  if (EverParseIsError(positionAftercol1))
  {
    return positionAftercol1;
  }
  /* Field _enum_constraint_x */
  uint64_t
  positionAfterEnumConstraint0 =
    ValidateEnumConstraintX(col,
      Ctxt,
      Err,
      Input,
      positionAftercol1);
  if (EverParseIsSuccess(positionAfterEnumConstraint0))
  {
    return positionAfterEnumConstraint0;
  }
  Err("_enum_constraint",
    "x",
    EverParseErrorReasonOfResult(positionAfterEnumConstraint0),
    Ctxt,
    Input,
    positionAftercol1);
  return positionAfterEnumConstraint0;
}

