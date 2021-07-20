

#include "Base.h"

/*
Auto-generated field identifier for error reporting
*/
#define BASE__PAIR__FIRST ((uint64_t)7U)

/*
Auto-generated field identifier for error reporting
*/
#define BASE__PAIR__SECOND ((uint64_t)8U)

uint64_t BaseValidateUlong(EverParseInputBuffer Sl)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Sl.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Sl.len - currentPosition);
  if (hasBytes)
  {
    return (uint64_t)(uint32_t)4U;
  }
  return EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
}

static inline uint64_t ValidatePairFirst(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _Pair_first
        of type Base._Pair
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field first */
  uint64_t result = BaseValidateUlong(Input);
  return EverParseMaybeSetErrorCode(result, startPosition1, BASE__PAIR__FIRST);
}

static inline uint64_t ValidatePairSecond(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _Pair_second
        of type Base._Pair
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field second */
  uint64_t result = BaseValidateUlong(Input);
  return EverParseMaybeSetErrorCode(result, startPosition1, BASE__PAIR__SECOND);
}

uint64_t BaseValidatePair(EverParseInputBuffer Input)
{
  /* Field _Pair_first */
  uint64_t res = ValidatePairFirst(Input);
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  uint64_t resultAfterfirst = res;
  if (EverParseIsError(resultAfterfirst))
  {
    return resultAfterfirst;
  }
  /* Field _Pair_second */
  uint64_t res0 = ValidatePairSecond(Input);
  if (EverParseIsSuccess(res0))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res0;
  }
  return res0;
}

