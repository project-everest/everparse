

#include "Base.h"

/*
Auto-generated field identifier for error reporting
*/
#define BASE__PAIR__FIRST ((uint64_t)7U)

/*
Auto-generated field identifier for error reporting
*/
#define BASE__PAIR__SECOND ((uint64_t)8U)

uint64_t BaseValidateUlong(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    return EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return StartPosition + (uint64_t)4U;
}

static inline uint64_t
ValidatePairFirst(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Pair_first
        of type Base._Pair
--*/
{
  /* Validating field first */
  uint64_t endPositionOrError = BaseValidateUlong(InputLength, Input, StartPosition);
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, BASE__PAIR__FIRST);
}

static inline uint64_t
ValidatePairSecond(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Pair_second
        of type Base._Pair
--*/
{
  /* Validating field second */
  uint64_t endPositionOrError = BaseValidateUlong(InputLength, Input, StartPosition);
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, BASE__PAIR__SECOND);
}

uint64_t BaseValidatePair(uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _Pair_first */
  uint64_t positionAfterfirst = ValidatePairFirst(Uu, Input, StartPosition);
  if (EverParseIsError(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  /* Field _Pair_second */
  return ValidatePairSecond(Uu, Input, positionAfterfirst);
}

