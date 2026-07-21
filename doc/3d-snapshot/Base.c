

#include "Base.h"

uint64_t
BaseValidateUlong(
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
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterUlong;
  if (hasBytes)
  {
    positionAfterUlong = StartPosition + 4ULL;
  }
  else
  {
    positionAfterUlong =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterUlong))
  {
    return positionAfterUlong;
  }
  ErrorHandlerFn("___ULONG",
    "missing",
    EverParseErrorReasonOfResult(positionAfterUlong),
    EverParseGetValidatorErrorKind(positionAfterUlong),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterUlong;
}

uint64_t
BaseValidatePair(
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
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  BOOLEAN hasBytes = 8ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 8ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

