

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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _point_x
        of type ColoredPoint._point
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint64_t)2U <= (InputLength - Pos);
  uint64_t positionAfterPoint;
  if (hasBytes)
  {
    positionAfterPoint = Pos + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  Err("_point", "_point_x", EverParseErrorReasonOfResult(positionAfterPoint), Ctxt, Input, Pos);
  return positionAfterPoint;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _point_y
        of type ColoredPoint._point
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint64_t)2U <= (InputLength - Pos);
  uint64_t positionAfterPoint;
  if (hasBytes)
  {
    positionAfterPoint = Pos + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  Err("_point", "_point_y", EverParseErrorReasonOfResult(positionAfterPoint), Ctxt, Input, Pos);
  return positionAfterPoint;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
{
  /* Field _point_x */
  uint64_t positionAfterPoint = ValidatePointX(Ctxt, Err, Input, InputLength, Pos);
  uint64_t res;
  if (EverParseIsSuccess(positionAfterPoint))
  {
    res = positionAfterPoint;
  }
  else
  {
    Err("_point", "x", EverParseErrorReasonOfResult(positionAfterPoint), Ctxt, Input, Pos);
    res = positionAfterPoint;
  }
  uint64_t positionAfterx = res;
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _point_y */
  uint64_t positionAfterPoint0 = ValidatePointY(Ctxt, Err, Input, InputLength, positionAfterx);
  if (EverParseIsSuccess(positionAfterPoint0))
  {
    return positionAfterPoint0;
  }
  Err("_point",
    "y",
    EverParseErrorReasonOfResult(positionAfterPoint0),
    Ctxt,
    Input,
    positionAfterx);
  return positionAfterPoint0;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _coloredPoint1_color
        of type ColoredPoint._coloredPoint1
--*/
{
  /* Validating field color */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint64_t)1U <= (InputLength - Pos);
  uint64_t positionAfterColoredPoint1;
  if (hasBytes)
  {
    positionAfterColoredPoint1 = Pos + (uint64_t)1U;
  }
  else
  {
    positionAfterColoredPoint1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    return positionAfterColoredPoint1;
  }
  Err("_coloredPoint1",
    "_coloredPoint1_color",
    EverParseErrorReasonOfResult(positionAfterColoredPoint1),
    Ctxt,
    Input,
    Pos);
  return positionAfterColoredPoint1;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _coloredPoint1_pt
        of type ColoredPoint._coloredPoint1
--*/
{
  /* Validating field pt */
  uint64_t positionAfterColoredPoint1 = ValidatePoint(Ctxt, Err, Input, InputLength, Pos);
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    return positionAfterColoredPoint1;
  }
  Err("_coloredPoint1",
    "_coloredPoint1_pt",
    EverParseErrorReasonOfResult(positionAfterColoredPoint1),
    Ctxt,
    Input,
    Pos);
  return positionAfterColoredPoint1;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
{
  /* Field _coloredPoint1_color */
  uint64_t
  positionAfterColoredPoint1 = ValidateColoredPoint1Color(Ctxt, Err, Input, InputLength, Pos);
  uint64_t res;
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    res = positionAfterColoredPoint1;
  }
  else
  {
    Err("_coloredPoint1",
      "color",
      EverParseErrorReasonOfResult(positionAfterColoredPoint1),
      Ctxt,
      Input,
      Pos);
    res = positionAfterColoredPoint1;
  }
  uint64_t positionAftercolor = res;
  if (EverParseIsError(positionAftercolor))
  {
    return positionAftercolor;
  }
  /* Field _coloredPoint1_pt */
  uint64_t
  positionAfterColoredPoint10 =
    ValidateColoredPoint1Pt(Ctxt,
      Err,
      Input,
      InputLength,
      positionAftercolor);
  if (EverParseIsSuccess(positionAfterColoredPoint10))
  {
    return positionAfterColoredPoint10;
  }
  Err("_coloredPoint1",
    "pt",
    EverParseErrorReasonOfResult(positionAfterColoredPoint10),
    Ctxt,
    Input,
    positionAftercolor);
  return positionAfterColoredPoint10;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _coloredPoint2_pt
        of type ColoredPoint._coloredPoint2
--*/
{
  /* Validating field pt */
  uint64_t positionAfterColoredPoint2 = ValidatePoint(Ctxt, Err, Input, InputLength, Pos);
  if (EverParseIsSuccess(positionAfterColoredPoint2))
  {
    return positionAfterColoredPoint2;
  }
  Err("_coloredPoint2",
    "_coloredPoint2_pt",
    EverParseErrorReasonOfResult(positionAfterColoredPoint2),
    Ctxt,
    Input,
    Pos);
  return positionAfterColoredPoint2;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _coloredPoint2_color
        of type ColoredPoint._coloredPoint2
--*/
{
  /* Validating field color */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint64_t)1U <= (InputLength - Pos);
  uint64_t positionAfterColoredPoint2;
  if (hasBytes)
  {
    positionAfterColoredPoint2 = Pos + (uint64_t)1U;
  }
  else
  {
    positionAfterColoredPoint2 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterColoredPoint2))
  {
    return positionAfterColoredPoint2;
  }
  Err("_coloredPoint2",
    "_coloredPoint2_color",
    EverParseErrorReasonOfResult(positionAfterColoredPoint2),
    Ctxt,
    Input,
    Pos);
  return positionAfterColoredPoint2;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t Pos
)
{
  /* Field _coloredPoint2_pt */
  uint64_t
  positionAfterColoredPoint2 = ValidateColoredPoint2Pt(Ctxt, Err, Input, InputLength, Pos);
  uint64_t positionAfterpt;
  if (EverParseIsSuccess(positionAfterColoredPoint2))
  {
    positionAfterpt = positionAfterColoredPoint2;
  }
  else
  {
    Err("_coloredPoint2",
      "pt",
      EverParseErrorReasonOfResult(positionAfterColoredPoint2),
      Ctxt,
      Input,
      Pos);
    positionAfterpt = positionAfterColoredPoint2;
  }
  if (EverParseIsError(positionAfterpt))
  {
    return positionAfterpt;
  }
  /* Field _coloredPoint2_color */
  uint64_t
  positionAfterColoredPoint20 =
    ValidateColoredPoint2Color(Ctxt,
      Err,
      Input,
      InputLength,
      positionAfterpt);
  if (EverParseIsSuccess(positionAfterColoredPoint20))
  {
    return positionAfterColoredPoint20;
  }
  Err("_coloredPoint2",
    "color",
    EverParseErrorReasonOfResult(positionAfterColoredPoint20),
    Ctxt,
    Input,
    positionAfterpt);
  return positionAfterColoredPoint20;
}

