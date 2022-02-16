

#include "ReadPair.h"


#include "EverParse.h"
uint64_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field first */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterfirst0;
  if (hasBytes0)
  {
    positionAfterfirst0 = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterfirst0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterPair;
  if (EverParseIsError(positionAfterfirst0))
  {
    positionAfterPair = positionAfterfirst0;
  }
  else
  {
    uint32_t first = Load32Le(Input + (uint32_t)StartPosition);
    *X = first;
    if (TRUE)
    {
      positionAfterPair = positionAfterfirst0;
    }
    else
    {
      positionAfterPair =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          EverParseGetValidatorErrorPos(positionAfterfirst0));
    }
  }
  uint64_t positionAfterfirst;
  if (EverParseIsSuccess(positionAfterPair))
  {
    positionAfterfirst = positionAfterPair;
  }
  else
  {
    Err("_Pair",
      "first",
      EverParseErrorReasonOfResult(positionAfterPair),
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
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - positionAfterfirst);
  uint64_t positionAftersecond;
  if (hasBytes)
  {
    positionAftersecond = positionAfterfirst + (uint64_t)4U;
  }
  else
  {
    positionAftersecond =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterfirst);
  }
  uint64_t positionAfterPair0;
  if (EverParseIsError(positionAftersecond))
  {
    positionAfterPair0 = positionAftersecond;
  }
  else
  {
    uint32_t second = Load32Le(Input + (uint32_t)positionAfterfirst);
    *Y = second;
    if (TRUE)
    {
      positionAfterPair0 = positionAftersecond;
    }
    else
    {
      positionAfterPair0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          EverParseGetValidatorErrorPos(positionAftersecond));
    }
  }
  if (EverParseIsSuccess(positionAfterPair0))
  {
    return positionAfterPair0;
  }
  Err("_Pair",
    "second",
    EverParseErrorReasonOfResult(positionAfterPair0),
    Ctxt,
    Input,
    positionAfterfirst);
  return positionAfterPair0;
}

