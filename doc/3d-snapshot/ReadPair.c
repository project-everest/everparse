

#include "ReadPair.h"

#include "EverParse.h"

uint64_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field first */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterfirst0;
  uint64_t positionAfterPair;
  uint32_t first;
  BOOLEAN actionResult;
  uint64_t positionAfterfirst;
  BOOLEAN hasBytes;
  uint64_t positionAftersecond;
  uint64_t positionAfterPair0;
  uint32_t second;
  BOOLEAN actionResult0;
  if (hasBytes0)
  {
    positionAfterfirst0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterfirst0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterfirst0))
  {
    positionAfterPair = positionAfterfirst0;
  }
  else
  {
    first = Load32Le(Input + (uint32_t)StartPosition);
    *X = first;
    actionResult = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionResult);
    positionAfterPair = positionAfterfirst0;
  }
  if (EverParseIsSuccess(positionAfterPair))
  {
    positionAfterfirst = positionAfterPair;
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
    positionAfterfirst = positionAfterPair;
  }
  if (EverParseIsError(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  /* Validating field second */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterfirst) >= 4ULL;
  if (hasBytes)
  {
    positionAftersecond = positionAfterfirst + 4ULL;
  }
  else
  {
    positionAftersecond =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterfirst);
  }
  if (EverParseIsError(positionAftersecond))
  {
    positionAfterPair0 = positionAftersecond;
  }
  else
  {
    second = Load32Le(Input + (uint32_t)positionAfterfirst);
    *Y = second;
    actionResult0 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionResult0);
    positionAfterPair0 = positionAftersecond;
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

