

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
  BOOLEAN hasBytesForColorPt = (InputLength - StartPosition) >= 5ULL;
  uint64_t res;
  uint64_t positionAfterColor;
  if (hasBytesForColorPt)
  {
    res = StartPosition + 5ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterColor = res;
  if (EverParseIsSuccess(positionAfterColor))
  {
    return positionAfterColor;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParseErrorReasonOfResult(positionAfterColor),
    EverParseGetValidatorErrorKind(positionAfterColor),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColor;
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
  BOOLEAN hasBytesForPtColor = (InputLength - StartPosition) >= 5ULL;
  uint64_t res;
  uint64_t positionAfterPt;
  if (hasBytesForPtColor)
  {
    res = StartPosition + 5ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterPt = res;
  if (EverParseIsSuccess(positionAfterPt))
  {
    return positionAfterPt;
  }
  ErrorHandlerFn("_coloredPoint2",
    "pt",
    EverParseErrorReasonOfResult(positionAfterPt),
    EverParseGetValidatorErrorKind(positionAfterPt),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPt;
}

