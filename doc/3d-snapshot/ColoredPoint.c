

#include "ColoredPoint.h"

static inline uint64_t
ValidatePoint(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (uint64_t)2U <= (InputLength - StartPosition);
  uint64_t positionAfterPoint;
  if (hasBytes0)
  {
    positionAfterPoint = StartPosition + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterPoint))
  {
    res = positionAfterPoint;
  }
  else
  {
    ErrorHandlerFn("_point",
      "x",
      EverParseErrorReasonOfResult(positionAfterPoint),
      EverParseGetValidatorErrorKind(positionAfterPoint),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterPoint;
  }
  uint64_t positionAfterx = res;
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint64_t)2U <= (InputLength - positionAfterx);
  uint64_t positionAfterPoint0;
  if (hasBytes)
  {
    positionAfterPoint0 = positionAfterx + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterx);
  }
  if (EverParseIsSuccess(positionAfterPoint0))
  {
    return positionAfterPoint0;
  }
  ErrorHandlerFn("_point",
    "y",
    EverParseErrorReasonOfResult(positionAfterPoint0),
    EverParseGetValidatorErrorKind(positionAfterPoint0),
    Ctxt,
    Input,
    positionAfterx);
  return positionAfterPoint0;
}

uint64_t
ColoredPointValidateColoredPoint1(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field color */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint64_t)1U <= (InputLength - StartPosition);
  uint64_t positionAfterColoredPoint1;
  if (hasBytes)
  {
    positionAfterColoredPoint1 = StartPosition + (uint64_t)1U;
  }
  else
  {
    positionAfterColoredPoint1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    res = positionAfterColoredPoint1;
  }
  else
  {
    ErrorHandlerFn("_coloredPoint1",
      "color",
      EverParseErrorReasonOfResult(positionAfterColoredPoint1),
      EverParseGetValidatorErrorKind(positionAfterColoredPoint1),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterColoredPoint1;
  }
  uint64_t positionAftercolor = res;
  if (EverParseIsError(positionAftercolor))
  {
    return positionAftercolor;
  }
  /* Validating field pt */
  uint64_t
  positionAfterColoredPoint10 =
    ValidatePoint(Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAftercolor);
  if (EverParseIsSuccess(positionAfterColoredPoint10))
  {
    return positionAfterColoredPoint10;
  }
  ErrorHandlerFn("_coloredPoint1",
    "pt",
    EverParseErrorReasonOfResult(positionAfterColoredPoint10),
    EverParseGetValidatorErrorKind(positionAfterColoredPoint10),
    Ctxt,
    Input,
    positionAftercolor);
  return positionAfterColoredPoint10;
}

uint64_t
ColoredPointValidateColoredPoint2(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field pt */
  uint64_t
  positionAfterColoredPoint2 =
    ValidatePoint(Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      StartPosition);
  uint64_t positionAfterpt;
  if (EverParseIsSuccess(positionAfterColoredPoint2))
  {
    positionAfterpt = positionAfterColoredPoint2;
  }
  else
  {
    ErrorHandlerFn("_coloredPoint2",
      "pt",
      EverParseErrorReasonOfResult(positionAfterColoredPoint2),
      EverParseGetValidatorErrorKind(positionAfterColoredPoint2),
      Ctxt,
      Input,
      StartPosition);
    positionAfterpt = positionAfterColoredPoint2;
  }
  if (EverParseIsError(positionAfterpt))
  {
    return positionAfterpt;
  }
  /* Validating field color */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint64_t)1U <= (InputLength - positionAfterpt);
  uint64_t positionAfterColoredPoint20;
  if (hasBytes)
  {
    positionAfterColoredPoint20 = positionAfterpt + (uint64_t)1U;
  }
  else
  {
    positionAfterColoredPoint20 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterpt);
  }
  if (EverParseIsSuccess(positionAfterColoredPoint20))
  {
    return positionAfterColoredPoint20;
  }
  ErrorHandlerFn("_coloredPoint2",
    "color",
    EverParseErrorReasonOfResult(positionAfterColoredPoint20),
    EverParseGetValidatorErrorKind(positionAfterColoredPoint20),
    Ctxt,
    Input,
    positionAfterpt);
  return positionAfterColoredPoint20;
}

