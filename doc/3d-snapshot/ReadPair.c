

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
  uint64_t positionAfterfirst1;
  uint32_t first;
  BOOLEAN actionResult;
  uint64_t positionAfterfirst;
  BOOLEAN hasBytes;
  uint64_t positionAftersecond0;
  uint64_t positionAftersecond;
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
    positionAfterfirst1 = positionAfterfirst0;
  }
  else
  {
    first = Load32Le(Input + (uint32_t)StartPosition);
    *X = first;
    actionResult = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionResult);
    positionAfterfirst1 = positionAfterfirst0;
  }
  if (EverParseIsSuccess(positionAfterfirst1))
  {
    positionAfterfirst = positionAfterfirst1;
  }
  else
  {
    ErrorHandlerFn("_Pair",
      "first",
      EverParseErrorReasonOfResult(positionAfterfirst1),
      EverParseGetValidatorErrorKind(positionAfterfirst1),
      Ctxt,
      Input,
      StartPosition);
    positionAfterfirst = positionAfterfirst1;
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
    positionAftersecond0 = positionAfterfirst + 4ULL;
  }
  else
  {
    positionAftersecond0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterfirst);
  }
  if (EverParseIsError(positionAftersecond0))
  {
    positionAftersecond = positionAftersecond0;
  }
  else
  {
    second = Load32Le(Input + (uint32_t)positionAfterfirst);
    *Y = second;
    actionResult0 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionResult0);
    positionAftersecond = positionAftersecond0;
  }
  if (EverParseIsSuccess(positionAftersecond))
  {
    return positionAftersecond;
  }
  ErrorHandlerFn("_Pair",
    "second",
    EverParseErrorReasonOfResult(positionAftersecond),
    EverParseGetValidatorErrorKind(positionAftersecond),
    Ctxt,
    Input,
    positionAfterfirst);
  return positionAftersecond;
}

