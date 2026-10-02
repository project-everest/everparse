

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
  uint64_t resForColorPt;
  uint64_t positionAfterColorOrError;
  if (hasBytesForColorPt)
  {
    resForColorPt = StartPosition + 5ULL;
  }
  else
  {
    resForColorPt =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterColorOrError = resForColorPt;
  if (EverParseIsSuccess(positionAfterColorOrError))
  {
    return positionAfterColorOrError;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParseErrorReasonOfResult(positionAfterColorOrError),
    EverParseGetValidatorErrorKind(positionAfterColorOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColorOrError;
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
  uint64_t resForPtColor;
  uint64_t positionAfterPtOrError;
  if (hasBytesForPtColor)
  {
    resForPtColor = StartPosition + 5ULL;
  }
  else
  {
    resForPtColor =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterPtOrError = resForPtColor;
  if (EverParseIsSuccess(positionAfterPtOrError))
  {
    return positionAfterPtOrError;
  }
  ErrorHandlerFn("_coloredPoint2",
    "pt",
    EverParseErrorReasonOfResult(positionAfterPtOrError),
    EverParseGetValidatorErrorKind(positionAfterPtOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPtOrError;
}

