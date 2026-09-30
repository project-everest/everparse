

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
  BOOLEAN hasBytesForCorners = (InputLength - StartPosition) >= (uint64_t)12U;
  uint64_t resForCorners;
  uint64_t positionAfterCorners;
  if (hasBytesForCorners)
  {
    resForCorners = StartPosition + (uint64_t)12U;
  }
  else
  {
    resForCorners =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterCorners = resForCorners;
  if (EverParseIsSuccess(positionAfterCorners))
  {
    return positionAfterCorners;
  }
  ErrorHandlerFn("_triangle",
    "corners",
    EverParseErrorReasonOfResult(positionAfterCorners),
    EverParseGetValidatorErrorKind(positionAfterCorners),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterCorners;
}

