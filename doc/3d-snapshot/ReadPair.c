

#include "ReadPair.h"

/*
Auto-generated field identifier for error reporting
*/
#define READPAIR__PAIR__FIRST ((uint64_t)35U)

/*
Auto-generated field identifier for error reporting
*/
#define READPAIR__PAIR__SECOND ((uint64_t)36U)

static inline uint64_t
ValidatePairFirst(uint32_t *X, uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Pair_first
        of type ReadPair._Pair
--*/
{
  /* Validating field first */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterPairFirst;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    positionAfterPairFirst = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterPairFirst = StartPosition + (uint64_t)4U;
  }
  uint64_t endPositionOrError;
  if (EverParseIsError(positionAfterPairFirst))
  {
    endPositionOrError = positionAfterPairFirst;
  }
  else
  {
    uint8_t *base = Input;
    uint32_t pairFirst = Load32Le(base + (uint32_t)StartPosition);
    *X = pairFirst;
    if (TRUE)
    {
      endPositionOrError = positionAfterPairFirst;
    }
    else
    {
      endPositionOrError = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, READPAIR__PAIR__FIRST);
}

static inline uint64_t
ValidatePairSecond(uint32_t *Y, uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Pair_second
        of type ReadPair._Pair
--*/
{
  /* Validating field second */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterPairSecond;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    positionAfterPairSecond = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterPairSecond = StartPosition + (uint64_t)4U;
  }
  uint64_t endPositionOrError;
  if (EverParseIsError(positionAfterPairSecond))
  {
    endPositionOrError = positionAfterPairSecond;
  }
  else
  {
    uint8_t *base = Input;
    uint32_t pairSecond = Load32Le(base + (uint32_t)StartPosition);
    *Y = pairSecond;
    if (TRUE)
    {
      endPositionOrError = positionAfterPairSecond;
    }
    else
    {
      endPositionOrError = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, READPAIR__PAIR__SECOND);
}

uint64_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
  uint32_t Uu,
  uint8_t *Input,
  uint64_t StartPosition
)
{
  /* Field _Pair_first */
  uint64_t positionAfterfirst = ValidatePairFirst(X, Uu, Input, StartPosition);
  if (EverParseIsError(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  /* Field _Pair_second */
  return ValidatePairSecond(Y, Uu, Input, positionAfterfirst);
}

