

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
  BOOLEAN hasBytesForFirst = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterFirst0;
  uint64_t positionAfterFirstOrError;
  uint32_t first;
  BOOLEAN actionResultForFirst;
  uint64_t positionAfterFirst;
  BOOLEAN hasBytesForSecond;
  uint64_t positionAfterSecond;
  uint64_t positionAfterSecondOrError;
  uint32_t second;
  BOOLEAN actionResultForSecond;
  if (hasBytesForFirst)
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
    positionAfterFirstOrError = positionAfterFirst0;
  }
  else
  {
    first = Load32Le(Input + (uint32_t)StartPosition);
    *X = first;
    actionResultForFirst = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionResultForFirst);
    positionAfterFirstOrError = positionAfterFirst0;
  }
  if (EverParseIsSuccess(positionAfterFirstOrError))
  {
    positionAfterFirst = positionAfterFirstOrError;
  }
  else
  {
    ErrorHandlerFn("_Pair",
      "first",
      EverParseErrorReasonOfResult(positionAfterFirstOrError),
      EverParseGetValidatorErrorKind(positionAfterFirstOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterFirst = positionAfterFirstOrError;
  }
  if (EverParseIsError(positionAfterFirst))
  {
    return positionAfterFirst;
  }
  /* Validating field second */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytesForSecond = (InputLength - positionAfterFirst) >= 4ULL;
  if (hasBytesForSecond)
  {
    positionAfterSecond = positionAfterFirst + 4ULL;
  }
  else
  {
    positionAfterSecond =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterFirst);
  }
  if (EverParseIsError(positionAfterSecond))
  {
    positionAfterSecondOrError = positionAfterSecond;
  }
  else
  {
    second = Load32Le(Input + (uint32_t)positionAfterFirst);
    *Y = second;
    actionResultForSecond = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionResultForSecond);
    positionAfterSecondOrError = positionAfterSecond;
  }
  if (EverParseIsSuccess(positionAfterSecondOrError))
  {
    return positionAfterSecondOrError;
  }
  ErrorHandlerFn("_Pair",
    "second",
    EverParseErrorReasonOfResult(positionAfterSecondOrError),
    EverParseGetValidatorErrorKind(positionAfterSecondOrError),
    Ctxt,
    Input,
    positionAfterFirst);
  return positionAfterSecondOrError;
}

