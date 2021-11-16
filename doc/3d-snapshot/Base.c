

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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterUlong;
  if (hasBytes)
  {
    positionAfterUlong = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterUlong =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterUlong))
  {
    return positionAfterUlong;
  }
  Err("___ULONG",
    "missing",
    EverParseErrorReasonOfResult(positionAfterUlong),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterUlong;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field first */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterPair;
  if (hasBytes0)
  {
    positionAfterPair = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterPair =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterPair))
  {
    res = positionAfterPair;
  }
  else
  {
    Err("_Pair",
      "first",
      EverParseErrorReasonOfResult(positionAfterPair),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterPair;
  }
  uint64_t positionAfterfirst = res;
  if (EverParseIsError(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  /* Validating field second */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - positionAfterfirst);
  uint64_t positionAfterPair0;
  if (hasBytes)
  {
    positionAfterPair0 = positionAfterfirst + (uint64_t)4U;
  }
  else
  {
    positionAfterPair0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterfirst);
  }
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

uint64_t
BaseValidateMine(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field f */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = (uint64_t)1U <= (InputLength - StartPosition);
  uint64_t positionAfterMine;
  if (hasBytes0)
  {
    positionAfterMine = StartPosition + (uint64_t)1U;
  }
  else
  {
    positionAfterMine =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterMine))
  {
    res = positionAfterMine;
  }
  else
  {
    Err("_Mine", "f", EverParseErrorReasonOfResult(positionAfterMine), Ctxt, Input, StartPosition);
    res = positionAfterMine;
  }
  uint64_t positionAfterf = res;
  if (EverParseIsError(positionAfterf))
  {
    return positionAfterf;
  }
  /* Validating field g */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint64_t)1U <= (InputLength - positionAfterf);
  uint64_t positionAfterMine0;
  if (hasBytes)
  {
    positionAfterMine0 = positionAfterf + (uint64_t)1U;
  }
  else
  {
    positionAfterMine0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterf);
  }
  if (EverParseIsSuccess(positionAfterMine0))
  {
    return positionAfterMine0;
  }
  Err("_Mine",
    "g",
    EverParseErrorReasonOfResult(positionAfterMine0),
    Ctxt,
    Input,
    positionAfterf);
  return positionAfterMine0;
}

