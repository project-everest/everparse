

#include "Triangle2.h"

uint64_t
Triangle2ValidateTriangle(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field corners */
  BOOLEAN hasBytes = (uint64_t)12U <= (InputLength - StartPosition);
  uint64_t res;
  if (hasBytes)
  {
    res = StartPosition + (uint64_t)12U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  uint64_t positionAfterTriangle = res;
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

