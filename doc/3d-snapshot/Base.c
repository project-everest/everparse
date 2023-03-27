

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
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterUlong;
  if (hasBytes)
  {
    positionAfterUlong = StartPosition + (uint64_t)4U;
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
  /* Validating field first */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterPair;
  if (hasBytes0)
  {
    positionAfterPair = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterPair =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterPair))
  {
    res = positionAfterPair;
  }
  else
  {
    ErrorHandlerFn("_Pair",
      "first",
      EverParseErrorReasonOfResult(positionAfterPair),
      EverParseGetValidatorErrorKind(positionAfterPair),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterPair;
  }
  uint64_t positionAfterfirst = res;
  if (EverParseIsError(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  /* Validating field second */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - positionAfterfirst);
  uint64_t positionAfterPair0;
  if (hasBytes)
  {
    positionAfterPair0 = positionAfterfirst + (uint64_t)4U;
  }
  else
  {
    positionAfterPair0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterfirst);
  }
  if (EverParseIsSuccess(positionAfterPair0))
  {
    return positionAfterPair0;
  }
  ErrorHandlerFn("_Pair",
    "second",
    EverParseErrorReasonOfResult(positionAfterPair0),
    EverParseGetValidatorErrorKind(positionAfterPair0),
    Ctxt,
    Input,
    positionAfterfirst);
  return positionAfterPair0;
}

