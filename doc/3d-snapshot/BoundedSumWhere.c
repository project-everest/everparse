

#include "BoundedSumWhere.h"

static inline uint64_t
ValidateBoundedSumLeft(
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
/*++
    Internal helper function:
        Validator for field _boundedSum_left
        of type BoundedSumWhere._boundedSum
--*/
{
  /* Validating field left */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterBoundedSum;
  if (hasBytes)
  {
    positionAfterBoundedSum = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterBoundedSum =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    return positionAfterBoundedSum;
  }
  Err("_boundedSum",
    "_boundedSum_left",
    EverParseErrorReasonOfResult(positionAfterBoundedSum),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterBoundedSum;
}

static inline uint64_t
ValidateBoundedSumRight(
  uint32_t Bound,
  uint32_t Left,
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
/*++
    Internal helper function:
        Validator for field _boundedSum_right
        of type BoundedSumWhere._boundedSum
--*/
{
  /* Validating field right */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterBoundedSum;
  if (hasBytes)
  {
    positionAfterBoundedSum = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterBoundedSum =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterBoundedSum0;
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    positionAfterBoundedSum0 = positionAfterBoundedSum;
  }
  else
  {
    Err("_boundedSum",
      "_boundedSum_right",
      EverParseErrorReasonOfResult(positionAfterBoundedSum),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBoundedSum0 = positionAfterBoundedSum;
  }
  uint64_t positionAfterBoundedSum1;
  if (EverParseIsError(positionAfterBoundedSum0))
  {
    positionAfterBoundedSum1 = positionAfterBoundedSum0;
  }
  else
  {
    /* reading field value */
    uint32_t res = Load32Le(Input + (uint32_t)StartPosition);
    uint32_t res0 = res;
    uint32_t boundedSum1 = res0;
    /* start: checking constraint */
    BOOLEAN boundedSumConstraintIsOk = Left <= Bound && boundedSum1 <= (Bound - Left);
    /* end: checking constraint */
    positionAfterBoundedSum1 =
      EverParseCheckConstraintOk(boundedSumConstraintIsOk,
        positionAfterBoundedSum0);
  }
  if (EverParseIsSuccess(positionAfterBoundedSum1))
  {
    return positionAfterBoundedSum1;
  }
  Err("_boundedSum",
    "_boundedSum_right.refinement",
    EverParseErrorReasonOfResult(positionAfterBoundedSum1),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterBoundedSum1;
}

uint64_t
BoundedSumWhereValidateBoundedSum(
  uint32_t Bound,
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
  /* Validating field __precondition */
  BOOLEAN preconditionConstraintIsOk = Bound <= (uint32_t)(uint16_t)1729U;
  uint64_t
  positionAfterPrecondition =
    EverParseCheckConstraintOk(preconditionConstraintIsOk,
      StartPosition);
  if (EverParseIsError(positionAfterPrecondition))
  {
    return positionAfterPrecondition;
  }
  /* Field _boundedSum_left */
  uint64_t
  positionAfterBoundedSum =
    ValidateBoundedSumLeft(Ctxt,
      Err,
      Input,
      InputLength,
      positionAfterPrecondition);
  uint64_t positionAfterleft;
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    positionAfterleft = positionAfterBoundedSum;
  }
  else
  {
    Err("_boundedSum",
      "left",
      EverParseErrorReasonOfResult(positionAfterBoundedSum),
      Ctxt,
      Input,
      positionAfterPrecondition);
    positionAfterleft = positionAfterBoundedSum;
  }
  if (EverParseIsError(positionAfterleft))
  {
    return positionAfterleft;
  }
  uint32_t res = Load32Le(Input + (uint32_t)positionAfterPrecondition);
  uint32_t res0 = res;
  uint32_t left = res0;
  /* Field _boundedSum_right */
  uint64_t
  positionAfterBoundedSum0 =
    ValidateBoundedSumRight(Bound,
      left,
      Ctxt,
      Err,
      Input,
      InputLength,
      positionAfterleft);
  if (EverParseIsSuccess(positionAfterBoundedSum0))
  {
    return positionAfterBoundedSum0;
  }
  Err("_boundedSum",
    "right",
    EverParseErrorReasonOfResult(positionAfterBoundedSum0),
    Ctxt,
    Input,
    positionAfterleft);
  return positionAfterBoundedSum0;
}

