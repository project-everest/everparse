

#include "HelloWorld.h"

#include "EverParse.h"

uint64_t
HelloWorldValidatePoint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytesForXY = (InputLength - StartPosition) >= 4ULL;
  uint64_t resForXY;
  uint64_t positionAfterXOrError;
  if (hasBytesForXY)
  {
    resForXY = StartPosition + 4ULL;
  }
  else
  {
    resForXY =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterXOrError = resForXY;
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    return positionAfterXOrError;
  }
  ErrorHandlerFn("_point",
    "x",
    EverParseErrorReasonOfResult(positionAfterXOrError),
    EverParseGetValidatorErrorKind(positionAfterXOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterXOrError;
}

