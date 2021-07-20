

#include "ReadPair.h"

/*
Auto-generated field identifier for error reporting
*/
#define READPAIR__PAIR__FIRST ((uint64_t)35U)

/*
Auto-generated field identifier for error reporting
*/
#define READPAIR__PAIR__SECOND ((uint64_t)36U)

static inline uint64_t ValidatePairFirst(uint32_t *X, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _Pair_first
        of type ReadPair._Pair
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field first */
  uint32_t positionBeforePairFirst = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterPairFirst;
  if (hasBytes)
  {
    resultAfterPairFirst = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterPairFirst = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t result;
  if (EverParseIsError(resultAfterPairFirst))
  {
    result = resultAfterPairFirst;
  }
  else
  {
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    uint8_t *res = Input.buf + currentPosition;
    *Input.pos = currentPosition + (uint32_t)4U;
    uint8_t *temp1 = res;
    uint32_t res0 = Load32Le(temp1);
    uint32_t pairFirst = res0;
    *X = pairFirst;
    if (TRUE)
    {
      result = resultAfterPairFirst;
    }
    else
    {
      result = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, READPAIR__PAIR__FIRST);
}

static inline uint64_t ValidatePairSecond(uint32_t *Y, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _Pair_second
        of type ReadPair._Pair
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field second */
  uint32_t positionBeforePairSecond = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterPairSecond;
  if (hasBytes)
  {
    resultAfterPairSecond = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterPairSecond = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t result;
  if (EverParseIsError(resultAfterPairSecond))
  {
    result = resultAfterPairSecond;
  }
  else
  {
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    uint8_t *res = Input.buf + currentPosition;
    *Input.pos = currentPosition + (uint32_t)4U;
    uint8_t *temp1 = res;
    uint32_t res0 = Load32Le(temp1);
    uint32_t pairSecond = res0;
    *Y = pairSecond;
    if (TRUE)
    {
      result = resultAfterPairSecond;
    }
    else
    {
      result = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, READPAIR__PAIR__SECOND);
}

uint64_t ReadPairValidatePair(uint32_t *X, uint32_t *Y, EverParseInputBuffer Input)
{
  /* Field _Pair_first */
  uint64_t resultAfterfirst = ValidatePairFirst(X, Input);
  if (EverParseIsError(resultAfterfirst))
  {
    return resultAfterfirst;
  }
  /* Field _Pair_second */
  return ValidatePairSecond(Y, Input);
}

