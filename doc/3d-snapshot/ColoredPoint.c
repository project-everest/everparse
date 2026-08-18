

#include "ColoredPoint.h"

#include "EverParse.h"

uint64_t
ColoredPointValidateColoredPoint1(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 5ULL;
  uint64_t res;
  uint64_t positionAfterColoredPoint1;
  if (hasBytes)
  {
    res = StartPosition + 5ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterColoredPoint1 = res;
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    return positionAfterColoredPoint1;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParseErrorReasonOfResult(positionAfterColoredPoint1),
    EverParseGetValidatorErrorKind(positionAfterColoredPoint1),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColoredPoint1;
}

uint64_t
ColoredPointValidateColoredPoint2(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 5ULL;
  uint64_t res;
  uint64_t positionAfterColoredPoint2;
  if (hasBytes)
  {
    res = StartPosition + 5ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterColoredPoint2 = res;
  if (EverParseIsSuccess(positionAfterColoredPoint2))
  {
    return positionAfterColoredPoint2;
  }
  ErrorHandlerFn("_coloredPoint2",
    "pt",
    EverParseErrorReasonOfResult(positionAfterColoredPoint2),
    EverParseGetValidatorErrorKind(positionAfterColoredPoint2),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColoredPoint2;
}

