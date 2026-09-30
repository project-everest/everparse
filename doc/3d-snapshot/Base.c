

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
  BOOLEAN hasBytesForMissing = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterMissingOrError;
  if (hasBytesForMissing)
  {
    positionAfterMissingOrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterMissingOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterMissingOrError))
  {
    return positionAfterMissingOrError;
  }
  ErrorHandlerFn("___ULONG",
    "missing",
    EverParseErrorReasonOfResult(positionAfterMissingOrError),
    EverParseGetValidatorErrorKind(positionAfterMissingOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterMissingOrError;
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
  BOOLEAN hasBytesForFirstSecond = (InputLength - StartPosition) >= 8ULL;
  uint64_t resForFirstSecond;
  uint64_t positionAfterFirstOrError;
  if (hasBytesForFirstSecond)
  {
    resForFirstSecond = StartPosition + 8ULL;
  }
  else
  {
    resForFirstSecond =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterFirstOrError = resForFirstSecond;
  if (EverParseIsSuccess(positionAfterFirstOrError))
  {
    return positionAfterFirstOrError;
  }
  ErrorHandlerFn("_Pair",
    "first",
    EverParseErrorReasonOfResult(positionAfterFirstOrError),
    EverParseGetValidatorErrorKind(positionAfterFirstOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterFirstOrError;
}

