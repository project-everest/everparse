

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
  uint64_t positionAfterPoint;
  if (hasBytes)
  {
    res = StartPosition + 4ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterPoint = res;
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  ErrorHandlerFn("_point",
    "x",
    EverParseErrorReasonOfResult(positionAfterPoint),
    EverParseGetValidatorErrorKind(positionAfterPoint),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPoint;
}

