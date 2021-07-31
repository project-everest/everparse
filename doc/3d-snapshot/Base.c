

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
  EverParseInputBuffer Input,
  uint32_t Pos0
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - Pos0);
  uint64_t positionAfterUlong;
  if (hasBytes)
  {
    positionAfterUlong = (uint64_t)(Pos0 + (uint32_t)4U);
  }
  else
  {
    positionAfterUlong = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(positionAfterUlong))
  {
    return positionAfterUlong;
  }
  Err("___ULONG", "", EverParseErrorReasonOfResult(positionAfterUlong), Ctxt, Input, Pos0);
  return positionAfterUlong;
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
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _Pair_first
        of type Base._Pair
--*/
{
  /* Validating field first */
  uint64_t positionAfterPair = BaseValidateUlong(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterPair))
  {
    return positionAfterPair;
  }
  Err("_Pair", "_Pair_first", EverParseErrorReasonOfResult(positionAfterPair), Ctxt, Input, Pos);
  return positionAfterPair;
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
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _Pair_second
        of type Base._Pair
--*/
{
  /* Validating field second */
  uint64_t positionAfterPair = BaseValidateUlong(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterPair))
  {
    return positionAfterPair;
  }
  Err("_Pair",
    "_Pair_second",
    EverParseErrorReasonOfResult(positionAfterPair),
    Ctxt,
    Input,
    Pos);
  return positionAfterPair;
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
  EverParseInputBuffer Input,
  uint32_t Pos
)
{
  /* Field _Pair_first */
  uint64_t positionAfterPair = ValidatePairFirst(Ctxt, Err, Input, Pos);
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterPair))
  {
    res0 = positionAfterPair;
  }
  else
  {
    Err("_Pair", "first", EverParseErrorReasonOfResult(positionAfterPair), Ctxt, Input, Pos);
    res0 = positionAfterPair;
  }
  if (EverParseIsSuccess(res0))
  {
    
  }
  uint64_t positionAfterfirst = res0;
  if (EverParseIsError(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  /* Field _Pair_second */
  uint64_t
  positionAfterPair0 = ValidatePairSecond(Ctxt, Err, Input, (uint32_t)positionAfterfirst);
  uint64_t res;
  if (EverParseIsSuccess(positionAfterPair0))
  {
    res = positionAfterPair0;
  }
  else
  {
    Err("_Pair",
      "second",
      EverParseErrorReasonOfResult(positionAfterPair0),
      Ctxt,
      Input,
      (uint32_t)positionAfterfirst);
    res = positionAfterPair0;
  }
  if (EverParseIsSuccess(res))
  {
    
  }
  return res;
}

