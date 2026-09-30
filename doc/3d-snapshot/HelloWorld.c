

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
  uint64_t res;
  uint64_t positionAfterX;
  if (hasBytesForXY)
  {
    res = StartPosition + 4ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterX = res;
  if (EverParseIsSuccess(positionAfterX))
  {
    return positionAfterX;
  }
  ErrorHandlerFn("_point",
    "x",
    EverParseErrorReasonOfResult(positionAfterX),
    EverParseGetValidatorErrorKind(positionAfterX),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX;
}

