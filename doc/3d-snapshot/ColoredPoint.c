

#include "ColoredPoint.h"

static inline uint64_t
ValidatePointX(
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
        Validator for field _point_x
        of type ColoredPoint._point
--*/
{
  /* Validating field x */
  uint32_t positionBeforePoint = *Input.pos;
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - currentPosition);
  uint64_t resultAfterPoint;
  if (hasBytes)
  {
    resultAfterPoint = (uint64_t)(uint32_t)2U;
  }
  else
  {
    resultAfterPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterPoint))
  {
    return resultAfterPoint;
  }
  Err("_point",
    "_point_x",
    EverParseErrorReasonOfResult(resultAfterPoint),
    Ctxt,
    Input,
    positionBeforePoint);
  return resultAfterPoint;
}

static inline uint64_t
ValidatePointY(
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
        Validator for field _point_y
        of type ColoredPoint._point
--*/
{
  /* Validating field y */
  uint32_t positionBeforePoint = *Input.pos;
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - currentPosition);
  uint64_t resultAfterPoint;
  if (hasBytes)
  {
    resultAfterPoint = (uint64_t)(uint32_t)2U;
  }
  else
  {
    resultAfterPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterPoint))
  {
    return resultAfterPoint;
  }
  Err("_point",
    "_point_y",
    EverParseErrorReasonOfResult(resultAfterPoint),
    Ctxt,
    Input,
    positionBeforePoint);
  return resultAfterPoint;
}

static inline uint64_t
ValidatePoint(
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
  /* Field _point_x */
  uint32_t positionBeforePoint = *Input.pos;
  uint64_t resultAfterPoint = ValidatePointX(Ctxt, Err, Input);
  uint64_t res0;
  if (EverParseIsSuccess(resultAfterPoint))
  {
    res0 = resultAfterPoint;
  }
  else
  {
    Err("_point",
      "x",
      EverParseErrorReasonOfResult(resultAfterPoint),
      Ctxt,
      Input,
      positionBeforePoint);
    res0 = resultAfterPoint;
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
  /* Field _point_y */
  uint32_t positionBeforePoint0 = *Input.pos;
  uint64_t resultAfterPoint0 = ValidatePointY(Ctxt, Err, Input);
  uint64_t res;
  if (EverParseIsSuccess(resultAfterPoint0))
  {
    res = resultAfterPoint0;
  }
  else
  {
    Err("_point",
      "y",
      EverParseErrorReasonOfResult(resultAfterPoint0),
      Ctxt,
      Input,
      positionBeforePoint0);
    res = resultAfterPoint0;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

static inline uint64_t
ValidateColoredPoint1Color(
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
        Validator for field _coloredPoint1_color
        of type ColoredPoint._coloredPoint1
--*/
{
  /* Validating field color */
  uint32_t positionBeforeColoredPoint1 = *Input.pos;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - currentPosition);
  uint64_t resultAfterColoredPoint1;
  if (hasBytes)
  {
    resultAfterColoredPoint1 = (uint64_t)(uint32_t)1U;
  }
  else
  {
    resultAfterColoredPoint1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterColoredPoint1))
  {
    return resultAfterColoredPoint1;
  }
  Err("_coloredPoint1",
    "_coloredPoint1_color",
    EverParseErrorReasonOfResult(resultAfterColoredPoint1),
    Ctxt,
    Input,
    positionBeforeColoredPoint1);
  return resultAfterColoredPoint1;
}

static inline uint64_t
ValidateColoredPoint1Pt(
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
        Validator for field _coloredPoint1_pt
        of type ColoredPoint._coloredPoint1
--*/
{
  /* Validating field pt */
  uint32_t positionBeforeColoredPoint1 = *Input.pos;
  uint64_t resultAfterColoredPoint1 = ValidatePoint(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterColoredPoint1))
  {
    return resultAfterColoredPoint1;
  }
  Err("_coloredPoint1",
    "_coloredPoint1_pt",
    EverParseErrorReasonOfResult(resultAfterColoredPoint1),
    Ctxt,
    Input,
    positionBeforeColoredPoint1);
  return resultAfterColoredPoint1;
}

uint64_t
ColoredPointValidateColoredPoint1(
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
  /* Field _coloredPoint1_color */
  uint32_t positionBeforeColoredPoint1 = *Input.pos;
  uint64_t resultAfterColoredPoint1 = ValidateColoredPoint1Color(Ctxt, Err, Input);
  uint64_t res;
  if (EverParseIsSuccess(resultAfterColoredPoint1))
  {
    res = resultAfterColoredPoint1;
  }
  else
  {
    Err("_coloredPoint1",
      "color",
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
  uint64_t resultAftercolor = res;
  if (EverParseIsError(resultAftercolor))
  {
    return resultAftercolor;
  }
  /* Field _coloredPoint1_pt */
  uint32_t positionBeforeColoredPoint10 = *Input.pos;
  uint64_t resultAfterColoredPoint10 = ValidateColoredPoint1Pt(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterColoredPoint10))
  {
    return resultAfterColoredPoint10;
  }
  Err("_coloredPoint1",
    "pt",
    EverParseErrorReasonOfResult(resultAfterColoredPoint10),
    Ctxt,
    Input,
    positionBeforeColoredPoint10);
  return resultAfterColoredPoint10;
}

static inline uint64_t
ValidateColoredPoint2Pt(
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
        Validator for field _coloredPoint2_pt
        of type ColoredPoint._coloredPoint2
--*/
{
  /* Validating field pt */
  uint32_t positionBeforeColoredPoint2 = *Input.pos;
  uint64_t resultAfterColoredPoint2 = ValidatePoint(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterColoredPoint2))
  {
    return resultAfterColoredPoint2;
  }
  Err("_coloredPoint2",
    "_coloredPoint2_pt",
    EverParseErrorReasonOfResult(resultAfterColoredPoint2),
    Ctxt,
    Input,
    positionBeforeColoredPoint2);
  return resultAfterColoredPoint2;
}

static inline uint64_t
ValidateColoredPoint2Color(
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
        Validator for field _coloredPoint2_color
        of type ColoredPoint._coloredPoint2
--*/
{
  /* Validating field color */
  uint32_t positionBeforeColoredPoint2 = *Input.pos;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - currentPosition);
  uint64_t resultAfterColoredPoint2;
  if (hasBytes)
  {
    resultAfterColoredPoint2 = (uint64_t)(uint32_t)1U;
  }
  else
  {
    resultAfterColoredPoint2 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterColoredPoint2))
  {
    return resultAfterColoredPoint2;
  }
  Err("_coloredPoint2",
    "_coloredPoint2_color",
    EverParseErrorReasonOfResult(resultAfterColoredPoint2),
    Ctxt,
    Input,
    positionBeforeColoredPoint2);
  return resultAfterColoredPoint2;
}

uint64_t
ColoredPointValidateColoredPoint2(
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
  /* Field _coloredPoint2_pt */
  uint32_t positionBeforeColoredPoint2 = *Input.pos;
  uint64_t resultAfterColoredPoint2 = ValidateColoredPoint2Pt(Ctxt, Err, Input);
  uint64_t resultAfterpt;
  if (EverParseIsSuccess(resultAfterColoredPoint2))
  {
    resultAfterpt = resultAfterColoredPoint2;
  }
  else
  {
    Err("_coloredPoint2",
      "pt",
      EverParseErrorReasonOfResult(resultAfterColoredPoint2),
      Ctxt,
      Input,
      positionBeforeColoredPoint2);
    resultAfterpt = resultAfterColoredPoint2;
  }
  if (EverParseIsError(resultAfterpt))
  {
    return resultAfterpt;
  }
  /* Field _coloredPoint2_color */
  uint32_t positionBeforeColoredPoint20 = *Input.pos;
  uint64_t resultAfterColoredPoint20 = ValidateColoredPoint2Color(Ctxt, Err, Input);
  uint64_t res;
  if (EverParseIsSuccess(resultAfterColoredPoint20))
  {
    res = resultAfterColoredPoint20;
  }
  else
  {
    Err("_coloredPoint2",
      "color",
      EverParseErrorReasonOfResult(resultAfterColoredPoint20),
      Ctxt,
      Input,
      positionBeforeColoredPoint20);
    res = resultAfterColoredPoint20;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

