

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
  EverParseInputBuffer Input
)
{
  uint32_t positionBeforecolor = *Input.pos;
  uint32_t positionBeforecolor1 = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAftercolor0;
  if (hasBytes)
  {
    resultAftercolor0 = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAftercolor0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t resultAftercolor1;
  if (EverParseIsSuccess(resultAftercolor0))
  {
    resultAftercolor1 = resultAftercolor0;
  }
  else
  {
    Err("color",
      "",
      EverParseErrorReasonOfResult(resultAftercolor0),
      Ctxt,
      Input,
      positionBeforecolor1);
    resultAftercolor1 = resultAftercolor0;
  }
  uint64_t resultAftercolor;
  if (EverParseIsError(resultAftercolor1))
  {
    resultAftercolor = resultAftercolor1;
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
    uint32_t color = res0;
    /* start: checking constraint */
    BOOLEAN colorConstraintIsOk = color == RED || color == GREEN || color == BLUE || FALSE;
    /* end: checking constraint */
    resultAftercolor = EverParseCheckConstraintOk(colorConstraintIsOk, resultAftercolor1);
  }
  if (EverParseIsSuccess(resultAftercolor))
  {
    return resultAftercolor;
  }
  Err("color",
    ".refinement",
    EverParseErrorReasonOfResult(resultAftercolor),
    Ctxt,
    Input,
    positionBeforecolor);
  return resultAftercolor;
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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_col
        of type Color._coloredPoint
--*/
{
  /* Validating field col */
  uint32_t positionBeforeColoredPoint = *Input.pos;
  uint64_t resultAfterColoredPoint = ValidateColor(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterColoredPoint))
  {
    return resultAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_col",
    EverParseErrorReasonOfResult(resultAfterColoredPoint),
    Ctxt,
    Input,
    positionBeforeColoredPoint);
  return resultAfterColoredPoint;
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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_x
        of type Color._coloredPoint
--*/
{
  /* Validating field x */
  uint32_t positionBeforeColoredPoint = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterColoredPoint;
  if (hasBytes)
  {
    resultAfterColoredPoint = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterColoredPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterColoredPoint))
  {
    return resultAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_x",
    EverParseErrorReasonOfResult(resultAfterColoredPoint),
    Ctxt,
    Input,
    positionBeforeColoredPoint);
  return resultAfterColoredPoint;
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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _coloredPoint_y
        of type Color._coloredPoint
--*/
{
  /* Validating field y */
  uint32_t positionBeforeColoredPoint = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterColoredPoint;
  if (hasBytes)
  {
    resultAfterColoredPoint = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterColoredPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterColoredPoint))
  {
    return resultAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_y",
    EverParseErrorReasonOfResult(resultAfterColoredPoint),
    Ctxt,
    Input,
    positionBeforeColoredPoint);
  return resultAfterColoredPoint;
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
  EverParseInputBuffer Input
)
{
  /* Field _coloredPoint_col */
  uint32_t positionBeforeColoredPoint = *Input.pos;
  uint64_t resultAfterColoredPoint = ValidateColoredPointCol(Ctxt, Err, Input);
  uint64_t resultAftercol;
  if (EverParseIsSuccess(resultAfterColoredPoint))
  {
    resultAftercol = resultAfterColoredPoint;
  }
  else
  {
    Err("_coloredPoint",
      "col",
      EverParseErrorReasonOfResult(resultAfterColoredPoint),
      Ctxt,
      Input,
      positionBeforeColoredPoint);
    resultAftercol = resultAfterColoredPoint;
  }
  if (EverParseIsError(resultAftercol))
  {
    return resultAftercol;
  }
  /* Field _coloredPoint_x */
  uint32_t positionBeforeColoredPoint0 = *Input.pos;
  uint64_t resultAfterColoredPoint0 = ValidateColoredPointX(Ctxt, Err, Input);
  uint64_t res0;
  if (EverParseIsSuccess(resultAfterColoredPoint0))
  {
    res0 = resultAfterColoredPoint0;
  }
  else
  {
    Err("_coloredPoint",
      "x",
      EverParseErrorReasonOfResult(resultAfterColoredPoint0),
      Ctxt,
      Input,
      positionBeforeColoredPoint0);
    res0 = resultAfterColoredPoint0;
  }
  if (EverParseIsSuccess(res0))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res0;
  }
  uint64_t resultAfterx = res0;
  if (EverParseIsError(resultAfterx))
  {
    return resultAfterx;
  }
  /* Field _coloredPoint_y */
  uint32_t positionBeforeColoredPoint1 = *Input.pos;
  uint64_t resultAfterColoredPoint1 = ValidateColoredPointY(Ctxt, Err, Input);
  uint64_t res;
  if (EverParseIsSuccess(resultAfterColoredPoint1))
  {
    res = resultAfterColoredPoint1;
  }
  else
  {
    Err("_coloredPoint",
      "y",
      EverParseErrorReasonOfResult(resultAfterColoredPoint1),
      Ctxt,
      Input,
      positionBeforeColoredPoint1);
    res = resultAfterColoredPoint1;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

