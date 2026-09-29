

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
  uint64_t positionAftermissing;
  if (hasBytes)
  {
    positionAftermissing = StartPosition + 4ULL;
  }
  else
  {
    positionAftermissing =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAftermissing))
  {
    return positionAftermissing;
  }
  ErrorHandlerFn("___ULONG",
    "missing",
    EverParseErrorReasonOfResult(positionAftermissing),
    EverParseGetValidatorErrorKind(positionAftermissing),
    Ctxt,
    Input,
    StartPosition);
  return positionAftermissing;
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
  uint64_t positionAfterfirst;
  if (hasBytes)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterfirst = res;
  if (EverParseIsSuccess(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  ErrorHandlerFn("_Pair",
    "first",
    EverParseErrorReasonOfResult(positionAfterfirst),
    EverParseGetValidatorErrorKind(positionAfterfirst),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterfirst;
}

