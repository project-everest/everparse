

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
  uint64_t positionAfterMissing;
  if (hasBytes)
  {
    positionAfterMissing = StartPosition + 4ULL;
  }
  else
  {
    positionAfterMissing =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterMissing))
  {
    return positionAfterMissing;
  }
  ErrorHandlerFn("___ULONG",
    "missing",
    EverParseErrorReasonOfResult(positionAfterMissing),
    EverParseGetValidatorErrorKind(positionAfterMissing),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterMissing;
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
  uint64_t positionAfterFirst;
  if (hasBytes)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterFirst = res;
  if (EverParseIsSuccess(positionAfterFirst))
  {
    return positionAfterFirst;
  }
  ErrorHandlerFn("_Pair",
    "first",
    EverParseErrorReasonOfResult(positionAfterFirst),
    EverParseGetValidatorErrorKind(positionAfterFirst),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterFirst;
}

