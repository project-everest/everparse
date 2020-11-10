

#include "OrderedPair.h"

/*
Auto-generated field identifier for error reporting
*/
#define ORDEREDPAIR__LESSER ((uint64_t)1U)

/*
Auto-generated field identifier for error reporting
*/
#define ORDEREDPAIR__GREATER ((uint64_t)2U)

static inline uint64_t ValidateOrderedPairLesser(uint32_t Uu, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _orderedPair_lesser
        of type _orderedPair
--*/
{
  /* Validating field lesser */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, ORDEREDPAIR__LESSER);
}

static inline uint64_t
ValidateOrderedPairGreater(
  uint32_t Lesser,
  uint32_t Uu,
  uint8_t *Input,
  uint64_t StartPosition
)
/*++
    Internal helper function:
        Validator for field _orderedPair_greater
        of type _orderedPair
--*/
{
  /* Validating field greater */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterOrderedPairGreater;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterOrderedPairGreater = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterOrderedPairGreater = StartPosition + (uint64_t)4U;
  }
  uint64_t endPositionOrError;
  if (EverParseIsError(positionAfterOrderedPairGreater))
  {
    endPositionOrError = positionAfterOrderedPairGreater;
  }
  else
  {
    /* reading field value */
    uint8_t *base = Input;
    uint32_t orderedPairGreater = Load32Le(base + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN orderedPairGreaterConstraintIsOk = Lesser <= orderedPairGreater;
    /* end: checking constraint */
    endPositionOrError =
      EverParseCheckConstraintOk(orderedPairGreaterConstraintIsOk,
        positionAfterOrderedPairGreater);
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, ORDEREDPAIR__GREATER);
}

uint64_t OrderedPairValidateOrderedPair(uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _orderedPair_lesser */
  uint64_t positionAfterlesser = ValidateOrderedPairLesser(Uu, StartPosition);
  if (EverParseIsError(positionAfterlesser))
  {
    return positionAfterlesser;
  }
  uint8_t *base = Input;
  uint32_t lesser = Load32Le(base + (uint32_t)StartPosition);
  /* Field _orderedPair_greater */
  return ValidateOrderedPairGreater(lesser, Uu, Input, positionAfterlesser);
}

