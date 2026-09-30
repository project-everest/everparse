

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
  BOOLEAN hasBytesForABC = (InputLength - StartPosition) >= 12ULL;
  uint64_t resForABC;
  uint64_t positionAfterA;
  if (hasBytesForABC)
  {
    resForABC = StartPosition + 12ULL;
  }
  else
  {
    resForABC =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterA = resForABC;
  if (EverParseIsSuccess(positionAfterA))
  {
    return positionAfterA;
  }
  ErrorHandlerFn("_triangle",
    "a",
    EverParseErrorReasonOfResult(positionAfterA),
    EverParseGetValidatorErrorKind(positionAfterA),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterA;
}

