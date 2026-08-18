

#include "Base.h"

#include "EverParse.h"

uint64_t
BaseValidateUlong(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 4ULL;
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
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterPair;
  if (hasBytes)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterPair = res;
  if (EverParseIsSuccess(positionAfterPair))
  {
    return positionAfterPair;
  }
  ErrorHandlerFn("_Pair",
    "first",
    EverParseErrorReasonOfResult(positionAfterPair),
    EverParseGetValidatorErrorKind(positionAfterPair),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPair;
}

