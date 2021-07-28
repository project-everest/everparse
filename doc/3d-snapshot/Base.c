

#include "Base.h"

uint64_t
BaseValidateUlong(
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
  uint32_t positionBeforeUlong = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterUlong;
  if (hasBytes)
  {
    resultAfterUlong = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterUlong = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterUlong))
  {
    return resultAfterUlong;
  }
  Err("___ULONG",
    "",
    EverParseErrorReasonOfResult(resultAfterUlong),
    Ctxt,
    Input,
    positionBeforeUlong);
  return resultAfterUlong;
}

static inline uint64_t
ValidatePairFirst(
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
        of type Base._Pair
--*/
{
  /* Validating field first */
  uint32_t positionBeforePair = *Input.pos;
  uint64_t resultAfterPair = BaseValidateUlong(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterPair))
  {
    return resultAfterPair;
  }
  Err("_Pair",
    "_Pair_first",
    EverParseErrorReasonOfResult(resultAfterPair),
    Ctxt,
    Input,
    positionBeforePair);
  return resultAfterPair;
}

static inline uint64_t
ValidatePairSecond(
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
        of type Base._Pair
--*/
{
  /* Validating field second */
  uint32_t positionBeforePair = *Input.pos;
  uint64_t resultAfterPair = BaseValidateUlong(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterPair))
  {
    return resultAfterPair;
  }
  Err("_Pair",
    "_Pair_second",
    EverParseErrorReasonOfResult(resultAfterPair),
    Ctxt,
    Input,
    positionBeforePair);
  return resultAfterPair;
}

uint64_t
BaseValidatePair(
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
  uint64_t resultAfterPair = ValidatePairFirst(Ctxt, Err, Input);
  uint64_t res0;
  if (EverParseIsSuccess(resultAfterPair))
  {
    res0 = resultAfterPair;
  }
  else
  {
    Err("_Pair",
      "first",
      EverParseErrorReasonOfResult(resultAfterPair),
      Ctxt,
      Input,
      positionBeforePair);
    res0 = resultAfterPair;
  }
  if (EverParseIsSuccess(res0))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res0;
  }
  uint64_t resultAfterfirst = res0;
  if (EverParseIsError(resultAfterfirst))
  {
    return resultAfterfirst;
  }
  /* Field _Pair_second */
  uint32_t positionBeforePair0 = *Input.pos;
  uint64_t resultAfterPair0 = ValidatePairSecond(Ctxt, Err, Input);
  uint64_t res;
  if (EverParseIsSuccess(resultAfterPair0))
  {
    res = resultAfterPair0;
  }
  else
  {
    Err("_Pair",
      "second",
      EverParseErrorReasonOfResult(resultAfterPair0),
      Ctxt,
      Input,
      positionBeforePair0);
    res = resultAfterPair0;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

