

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
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 4ULL;
  uint64_t res;
  uint64_t positionAfterx;
  if (hasBytes)
  {
    res = StartPosition + 4ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterx = res;
  if (EverParseIsSuccess(positionAfterx))
  {
    return positionAfterx;
  }
  ErrorHandlerFn("_point",
    "x",
    EverParseErrorReasonOfResult(positionAfterx),
    EverParseGetValidatorErrorKind(positionAfterx),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterx;
}

