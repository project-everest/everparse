

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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos0
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - Pos0);
  uint64_t positionAftercolor0;
  if (hasBytes)
  {
    positionAftercolor0 = (uint64_t)(Pos0 + (uint32_t)4U);
  }
  else
  {
    positionAftercolor0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t positionAftercolor1;
  if (EverParseIsSuccess(positionAftercolor0))
  {
    positionAftercolor1 = positionAftercolor0;
  }
  else
  {
    Err("color", "", EverParseErrorReasonOfResult(positionAftercolor0), Ctxt, Input, Pos0);
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
    uint8_t *temp1 = Input.buf + Pos0;
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
    Pos0);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_col
        of type Color._coloredPoint
--*/
{
  /* Validating field col */
  uint64_t positionAfterColoredPoint = ValidateColor(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    return positionAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_col",
    EverParseErrorReasonOfResult(positionAfterColoredPoint),
    Ctxt,
    Input,
    Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_x
        of type Color._coloredPoint
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - Pos);
  uint64_t positionAfterColoredPoint;
  if (hasBytes)
  {
    positionAfterColoredPoint = (uint64_t)(Pos + (uint32_t)4U);
  }
  else
  {
    positionAfterColoredPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
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
    Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_y
        of type Color._coloredPoint
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - Pos);
  uint64_t positionAfterColoredPoint;
  if (hasBytes)
  {
    positionAfterColoredPoint = (uint64_t)(Pos + (uint32_t)4U);
  }
  else
  {
    positionAfterColoredPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
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
    Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
{
  /* Field _coloredPoint_col */
  uint64_t positionAfterColoredPoint = ValidateColoredPointCol(Ctxt, Err, Input, Pos);
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
      Pos);
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
      (uint32_t)positionAftercol);
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterColoredPoint0))
  {
    res0 = positionAfterColoredPoint0;
  }
  else
  {
    Err("_coloredPoint",
      "x",
      EverParseErrorReasonOfResult(positionAfterColoredPoint0),
      Ctxt,
      Input,
      (uint32_t)positionAftercol);
    res0 = positionAfterColoredPoint0;
  }
  if (EverParseIsSuccess(res0))
  {
    
  }
  uint64_t positionAfterx = res0;
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _coloredPoint_y */
  uint64_t
  positionAfterColoredPoint1 = ValidateColoredPointY(Ctxt, Err, Input, (uint32_t)positionAfterx);
  uint64_t res;
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    res = positionAfterColoredPoint1;
  }
  else
  {
    Err("_coloredPoint",
      "y",
      EverParseErrorReasonOfResult(positionAfterColoredPoint1),
      Ctxt,
      Input,
      (uint32_t)positionAfterx);
    res = positionAfterColoredPoint1;
  }
  if (EverParseIsSuccess(res))
  {
    
  }
  return res;
}

