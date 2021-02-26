

#include "Base.h"

/*
Auto-generated field identifier for error reporting
*/
#define BASE__PAIR__FIRST ((uint64_t)33U)

/*
Auto-generated field identifier for error reporting
*/
#define BASE__PAIR__SECOND ((uint64_t)34U)

/*
Auto-generated field identifier for error reporting
*/
#define BASE__DUMMY__DUMMY ((uint64_t)37U)

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

static inline uint64_t ValidateDummyDummy(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Dummy_dummy
        of type Base._Dummy
--*/
{
  /* Validating field dummy */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, BASE__DUMMY__DUMMY);
}

uint64_t BaseValidateDummy(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _Dummy_dummy */
  return ValidateDummyDummy(InputLength, StartPosition);
}

uint32_t BaseReadDummy(uint32_t InputLength, uint8_t *Input, uint32_t StartPosition)
{
  uint8_t *base = Input;
  return Load32Le(base + StartPosition);
}

