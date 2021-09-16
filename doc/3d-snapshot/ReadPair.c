

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
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _Pair_first
        of type ReadPair._Pair
--*/
{
  /* Validating field first */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterPair;
  if (hasBytes)
  {
    positionAfterPair = Pos + (uint64_t)4U;
  }
  else
  {
    positionAfterPair =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  uint64_t positionAfterPair0;
  if (EverParseIsSuccess(positionAfterPair))
  {
    positionAfterPair0 = positionAfterPair;
  }
  else
  {
    Err("_Pair",
      "_Pair_first.base",
      EverParseErrorReasonOfResult(positionAfterPair),
      Ctxt,
      Input,
      Pos);
    positionAfterPair0 = positionAfterPair;
  }
  uint64_t positionAfterPair1;
  if (EverParseIsError(positionAfterPair0))
  {
    positionAfterPair1 = positionAfterPair0;
  }
  else
  {
    uint8_t temp[4U] = { 0U };
    uint8_t *temp1 = Input.buf + (uint32_t)Pos;
    uint32_t res = Load32Le(temp1);
    uint32_t pair1 = res;
    *X = pair1;
    if (TRUE)
    {
      positionAfterPair1 = positionAfterPair0;
    }
    else
    {
      positionAfterPair1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          EverParseGetValidatorErrorPos(positionAfterPair0));
    }
  }
  if (EverParseIsSuccess(positionAfterPair1))
  {
    return positionAfterPair1;
  }
  Err("_Pair",
    "_Pair_first",
    EverParseErrorReasonOfResult(positionAfterPair1),
    Ctxt,
    Input,
    Pos);
  return positionAfterPair1;
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
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _Pair_second
        of type ReadPair._Pair
--*/
{
  /* Validating field second */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterPair;
  if (hasBytes)
  {
    positionAfterPair = Pos + (uint64_t)4U;
  }
  else
  {
    positionAfterPair =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  uint64_t positionAfterPair0;
  if (EverParseIsSuccess(positionAfterPair))
  {
    positionAfterPair0 = positionAfterPair;
  }
  else
  {
    Err("_Pair",
      "_Pair_second.base",
      EverParseErrorReasonOfResult(positionAfterPair),
      Ctxt,
      Input,
      Pos);
    positionAfterPair0 = positionAfterPair;
  }
  uint64_t positionAfterPair1;
  if (EverParseIsError(positionAfterPair0))
  {
    positionAfterPair1 = positionAfterPair0;
  }
  else
  {
    uint8_t temp[4U] = { 0U };
    uint8_t *temp1 = Input.buf + (uint32_t)Pos;
    uint32_t res = Load32Le(temp1);
    uint32_t pair1 = res;
    *Y = pair1;
    if (TRUE)
    {
      positionAfterPair1 = positionAfterPair0;
    }
    else
    {
      positionAfterPair1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          EverParseGetValidatorErrorPos(positionAfterPair0));
    }
  }
  if (EverParseIsSuccess(positionAfterPair1))
  {
    return positionAfterPair1;
  }
  Err("_Pair",
    "_Pair_second",
    EverParseErrorReasonOfResult(positionAfterPair1),
    Ctxt,
    Input,
    Pos);
  return positionAfterPair1;
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
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
{
  /* Field _Pair_first */
  uint64_t positionAfterPair = ValidatePairFirst(X, Ctxt, Err, Input, Pos);
  uint64_t positionAfterfirst;
  if (EverParseIsSuccess(positionAfterPair))
  {
    positionAfterfirst = positionAfterPair;
  }
  else
  {
    Err("_Pair", "first", EverParseErrorReasonOfResult(positionAfterPair), Ctxt, Input, Pos);
    positionAfterfirst = positionAfterPair;
  }
  if (EverParseIsError(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  /* Field _Pair_second */
  uint64_t positionAfterPair0 = ValidatePairSecond(Y, Ctxt, Err, Input, positionAfterfirst);
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

