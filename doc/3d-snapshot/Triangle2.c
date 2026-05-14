

#include "Triangle2.h"

#include "EverParse.h"

uint64_t
Triangle2ValidateTriangle(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field corners */
  BOOLEAN hasBytes = (InputLength - StartPosition) >= (uint64_t)12U;
  uint64_t res;
  uint64_t positionAfterTriangle;
  if (hasBytes)
  {
    res = StartPosition + (uint64_t)12U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterTriangle = res;
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  ErrorHandlerFn("_triangle",
    "corners",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    EverParseGetValidatorErrorKind(positionAfterTriangle),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTriangle;
}

