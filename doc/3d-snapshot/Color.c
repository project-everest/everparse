

#include "Color.h"

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
ValidateColor(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAftercolor0;
  if (hasBytes)
  {
    positionAftercolor0 = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAftercolor0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAftercolor1;
  if (EverParseIsSuccess(positionAftercolor0))
  {
    positionAftercolor1 = positionAftercolor0;
  }
  else
  {
    Err("color",
      "",
      EverParseErrorReasonOfResult(positionAftercolor0),
      Ctxt,
      Input,
      StartPosition);
    positionAftercolor1 = positionAftercolor0;
  }
  uint64_t positionAftercolor;
  if (EverParseIsError(positionAftercolor1))
  {
    positionAftercolor = positionAftercolor1;
  }
  else
  {
    /* reading field value */
    uint8_t temp[4U] = { 0U };
    uint8_t *temp1 = Input + (uint32_t)StartPosition;
    uint32_t res = Load32Le(temp1);
    uint32_t color = res;
    /* start: checking constraint */
    BOOLEAN colorConstraintIsOk = color == RED || color == GREEN || color == BLUE || FALSE;
    /* end: checking constraint */
    positionAftercolor = EverParseCheckConstraintOk(colorConstraintIsOk, positionAftercolor1);
  }
  if (EverParseIsSuccess(positionAftercolor))
  {
    return positionAftercolor;
  }
  Err("color",
    ".refinement",
    EverParseErrorReasonOfResult(positionAftercolor),
    Ctxt,
    Input,
    StartPosition);
  return positionAftercolor;
}

static inline uint64_t
ValidateColoredPointCol(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_col
        of type Color._coloredPoint
--*/
{
  /* Validating field col */
  uint64_t
  positionAfterColoredPoint = ValidateColor(Ctxt, Err, Input, InputLength, StartPosition);
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    return positionAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_col",
    EverParseErrorReasonOfResult(positionAfterColoredPoint),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColoredPoint;
}

static inline uint64_t
ValidateColoredPointX(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_x
        of type Color._coloredPoint
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterColoredPoint;
  if (hasBytes)
  {
    positionAfterColoredPoint = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterColoredPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    return positionAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_x",
    EverParseErrorReasonOfResult(positionAfterColoredPoint),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColoredPoint;
}

static inline uint64_t
ValidateColoredPointY(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_y
        of type Color._coloredPoint
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterColoredPoint;
  if (hasBytes)
  {
    positionAfterColoredPoint = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterColoredPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    return positionAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_y",
    EverParseErrorReasonOfResult(positionAfterColoredPoint),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColoredPoint;
}

uint64_t
ColorValidateColoredPoint(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Field _coloredPoint_col */
  uint64_t
  positionAfterColoredPoint =
    ValidateColoredPointCol(Ctxt,
      Err,
      Input,
      InputLength,
      StartPosition);
  uint64_t positionAftercol;
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    positionAftercol = positionAfterColoredPoint;
  }
  else
  {
    Err("_coloredPoint",
      "col",
      EverParseErrorReasonOfResult(positionAfterColoredPoint),
      Ctxt,
      Input,
      StartPosition);
    positionAftercol = positionAfterColoredPoint;
  }
  if (EverParseIsError(positionAftercol))
  {
    return positionAftercol;
  }
  /* Field _coloredPoint_x */
  uint64_t
  positionAfterColoredPoint0 =
    ValidateColoredPointX(Ctxt,
      Err,
      Input,
      InputLength,
      positionAftercol);
  uint64_t res;
  if (EverParseIsSuccess(positionAfterColoredPoint0))
  {
    res = positionAfterColoredPoint0;
  }
  else
  {
    Err("_coloredPoint",
      "x",
      EverParseErrorReasonOfResult(positionAfterColoredPoint0),
      Ctxt,
      Input,
      positionAftercol);
    res = positionAfterColoredPoint0;
  }
  uint64_t positionAfterx = res;
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _coloredPoint_y */
  uint64_t
  positionAfterColoredPoint1 =
    ValidateColoredPointY(Ctxt,
      Err,
      Input,
      InputLength,
      positionAfterx);
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    return positionAfterColoredPoint1;
  }
  Err("_coloredPoint",
    "y",
    EverParseErrorReasonOfResult(positionAfterColoredPoint1),
    Ctxt,
    Input,
    positionAfterx);
  return positionAfterColoredPoint1;
}

