

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
  uint64_t positionAfterFirst0;
  uint64_t positionAfterFirst1;
  uint32_t first;
  BOOLEAN actionResult;
  uint64_t positionAfterFirst;
  BOOLEAN hasBytes;
  uint64_t positionAfterSecond0;
  uint64_t positionAfterSecond;
  uint32_t second;
  BOOLEAN actionResult0;
  if (hasBytes0)
  {
    positionAfterFirst0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterFirst0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterFirst0))
  {
    positionAfterFirst1 = positionAfterFirst0;
  }
  else
  {
    first = Load32Le(Input + (uint32_t)StartPosition);
    *X = first;
    actionResult = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionResult);
    positionAfterFirst1 = positionAfterFirst0;
  }
  if (EverParseIsSuccess(positionAfterFirst1))
  {
    positionAfterFirst = positionAfterFirst1;
  }
  else
  {
    ErrorHandlerFn("_Pair",
      "first",
      EverParseErrorReasonOfResult(positionAfterFirst1),
      EverParseGetValidatorErrorKind(positionAfterFirst1),
      Ctxt,
      Input,
      StartPosition);
    positionAfterFirst = positionAfterFirst1;
  }
  if (EverParseIsError(positionAfterFirst))
  {
    return positionAfterFirst;
  }
  /* Validating field second */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterFirst) >= 4ULL;
  if (hasBytes)
  {
    positionAfterSecond0 = positionAfterFirst + 4ULL;
  }
  else
  {
    positionAfterSecond0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterFirst);
  }
  if (EverParseIsError(positionAfterSecond0))
  {
    positionAfterSecond = positionAfterSecond0;
  }
  else
  {
    second = Load32Le(Input + (uint32_t)positionAfterFirst);
    *Y = second;
    actionResult0 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionResult0);
    positionAfterSecond = positionAfterSecond0;
  }
  if (EverParseIsSuccess(positionAfterSecond))
  {
    return positionAfterSecond;
  }
  ErrorHandlerFn("_Pair",
    "second",
    EverParseErrorReasonOfResult(positionAfterSecond),
    EverParseGetValidatorErrorKind(positionAfterSecond),
    Ctxt,
    Input,
    positionAfterFirst);
  return positionAfterSecond;
}

