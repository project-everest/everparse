

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
  uint64_t positionAftercolor;
  if (hasBytes)
  {
    res = StartPosition + 5ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAftercolor = res;
  if (EverParseIsSuccess(positionAftercolor))
  {
    return positionAftercolor;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParseErrorReasonOfResult(positionAftercolor),
    EverParseGetValidatorErrorKind(positionAftercolor),
    Ctxt,
    Input,
    StartPosition);
  return positionAftercolor;
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
  uint64_t positionAfterpt;
  if (hasBytes)
  {
    res = StartPosition + 5ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterpt = res;
  if (EverParseIsSuccess(positionAfterpt))
  {
    return positionAfterpt;
  }
  ErrorHandlerFn("_coloredPoint2",
    "pt",
    EverParseErrorReasonOfResult(positionAfterpt),
    EverParseGetValidatorErrorKind(positionAfterpt),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterpt;
}

