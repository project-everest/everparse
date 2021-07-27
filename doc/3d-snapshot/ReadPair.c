

#include "ReadPair.h"

static inline uint64_t
ValidatePairFirst(
  uint32_t *X,
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _Pair_first
        of type ReadPair._Pair
--*/
{
  /* Validating field first */
  uint32_t positionBeforePair = *Input.pos;
  uint32_t positionBeforePair1 = *Input.pos;
  uint32_t positionBeforePair2 = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterPair;
  if (hasBytes)
  {
    resultAfterPair = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterPair = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t resultAfterPair0;
  if (EverParseIsSuccess(resultAfterPair))
  {
    resultAfterPair0 = resultAfterPair;
  }
  else
  {
    Err("_Pair",
      "_Pair_first.base",
      EverParseErrorReasonOfResult(resultAfterPair),
      Ctxt,
      Input,
      positionBeforePair2);
    resultAfterPair0 = resultAfterPair;
  }
  uint64_t resultAfterPair1;
  if (EverParseIsError(resultAfterPair0))
  {
    resultAfterPair1 = resultAfterPair0;
  }
  else
  {
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    uint8_t *res = Input.buf + currentPosition;
    *Input.pos = currentPosition + (uint32_t)4U;
    uint8_t *temp1 = res;
    uint32_t res0 = Load32Le(temp1);
    uint32_t pair1 = res0;
    *X = pair1;
    if (TRUE)
    {
      resultAfterPair1 = resultAfterPair0;
    }
    else
    {
      resultAfterPair1 = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
  }
  if (EverParseIsSuccess(resultAfterPair1))
  {
    return resultAfterPair1;
  }
  Err("_Pair",
    "_Pair_first",
    EverParseErrorReasonOfResult(resultAfterPair1),
    Ctxt,
    Input,
    positionBeforePair);
  return resultAfterPair1;
}

static inline uint64_t
ValidatePairSecond(
  uint32_t *Y,
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _Pair_second
        of type ReadPair._Pair
--*/
{
  /* Validating field second */
  uint32_t positionBeforePair = *Input.pos;
  uint32_t positionBeforePair1 = *Input.pos;
  uint32_t positionBeforePair2 = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterPair;
  if (hasBytes)
  {
    resultAfterPair = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterPair = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t resultAfterPair0;
  if (EverParseIsSuccess(resultAfterPair))
  {
    resultAfterPair0 = resultAfterPair;
  }
  else
  {
    Err("_Pair",
      "_Pair_second.base",
      EverParseErrorReasonOfResult(resultAfterPair),
      Ctxt,
      Input,
      positionBeforePair2);
    resultAfterPair0 = resultAfterPair;
  }
  uint64_t resultAfterPair1;
  if (EverParseIsError(resultAfterPair0))
  {
    resultAfterPair1 = resultAfterPair0;
  }
  else
  {
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    uint8_t *res = Input.buf + currentPosition;
    *Input.pos = currentPosition + (uint32_t)4U;
    uint8_t *temp1 = res;
    uint32_t res0 = Load32Le(temp1);
    uint32_t pair1 = res0;
    *Y = pair1;
    if (TRUE)
    {
      resultAfterPair1 = resultAfterPair0;
    }
    else
    {
      resultAfterPair1 = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
  }
  if (EverParseIsSuccess(resultAfterPair1))
  {
    return resultAfterPair1;
  }
  Err("_Pair",
    "_Pair_second",
    EverParseErrorReasonOfResult(resultAfterPair1),
    Ctxt,
    Input,
    positionBeforePair);
  return resultAfterPair1;
}

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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
{
  /* Field _Pair_first */
  uint32_t positionBeforePair = *Input.pos;
  uint64_t resultAfterPair = ValidatePairFirst(X, Ctxt, Err, Input);
  uint64_t resultAfterfirst;
  if (EverParseIsSuccess(resultAfterPair))
  {
    resultAfterfirst = resultAfterPair;
  }
  else
  {
    Err("_Pair",
      "first",
      EverParseErrorReasonOfResult(resultAfterPair),
      Ctxt,
      Input,
      positionBeforePair);
    resultAfterfirst = resultAfterPair;
  }
  if (EverParseIsError(resultAfterfirst))
  {
    return resultAfterfirst;
  }
  /* Field _Pair_second */
  uint32_t positionBeforePair0 = *Input.pos;
  uint64_t resultAfterPair0 = ValidatePairSecond(Y, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterPair0))
  {
    return resultAfterPair0;
  }
  Err("_Pair",
    "second",
    EverParseErrorReasonOfResult(resultAfterPair0),
    Ctxt,
    Input,
    positionBeforePair0);
  return resultAfterPair0;
}

