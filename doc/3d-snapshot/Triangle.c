

#include "Triangle.h"

#include "EverParse.h"

uint64_t
TriangleValidateTriangle(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 12ULL;
  uint64_t res;
  uint64_t positionAfterTriangle;
  if (hasBytes)
  {
    res = StartPosition + 12ULL;
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
    "a",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    EverParseGetValidatorErrorKind(positionAfterTriangle),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTriangle;
}

