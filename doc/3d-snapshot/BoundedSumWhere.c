

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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _boundedSum_left
        of type BoundedSumWhere._boundedSum
--*/
{
  /* Validating field left */
  uint32_t positionBeforeBoundedSum = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterBoundedSum;
  if (hasBytes)
  {
    resultAfterBoundedSum = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterBoundedSum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterBoundedSum))
  {
    return resultAfterBoundedSum;
  }
  Err("_boundedSum",
    "_boundedSum_left",
    EverParseErrorReasonOfResult(resultAfterBoundedSum),
    Ctxt,
    Input,
    positionBeforeBoundedSum);
  return resultAfterBoundedSum;
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _boundedSum_right
        of type BoundedSumWhere._boundedSum
--*/
{
  /* Validating field right */
  uint32_t positionBeforeBoundedSum = *Input.pos;
  uint32_t positionBeforeBoundedSum1 = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterBoundedSum;
  if (hasBytes)
  {
    resultAfterBoundedSum = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterBoundedSum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t resultAfterBoundedSum0;
  if (EverParseIsSuccess(resultAfterBoundedSum))
  {
    resultAfterBoundedSum0 = resultAfterBoundedSum;
  }
  else
  {
    Err("_boundedSum",
      "_boundedSum_right",
      EverParseErrorReasonOfResult(resultAfterBoundedSum),
      Ctxt,
      Input,
      positionBeforeBoundedSum1);
    resultAfterBoundedSum0 = resultAfterBoundedSum;
  }
  uint64_t resultAfterBoundedSum1;
  if (EverParseIsError(resultAfterBoundedSum0))
  {
    resultAfterBoundedSum1 = resultAfterBoundedSum0;
  }
  else
  {
    /* reading field value */
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    uint8_t *res = Input.buf + currentPosition;
    *Input.pos = currentPosition + (uint32_t)4U;
    uint8_t *temp1 = res;
    uint32_t res0 = Load32Le(temp1);
    uint32_t boundedSum1 = res0;
    /* start: checking constraint */
    BOOLEAN boundedSumConstraintIsOk = Left <= Bound && boundedSum1 <= (Bound - Left);
    /* end: checking constraint */
    resultAfterBoundedSum1 =
      EverParseCheckConstraintOk(boundedSumConstraintIsOk,
        resultAfterBoundedSum0);
  }
  if (EverParseIsSuccess(resultAfterBoundedSum1))
  {
    return resultAfterBoundedSum1;
  }
  Err("_boundedSum",
    "_boundedSum_right.refinement",
    EverParseErrorReasonOfResult(resultAfterBoundedSum1),
    Ctxt,
    Input,
    positionBeforeBoundedSum);
  return resultAfterBoundedSum1;
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field __precondition */
  BOOLEAN preconditionConstraintIsOk = Bound <= (uint32_t)(uint16_t)1729U;
  uint64_t
  resultAfterPrecondition =
    EverParseCheckConstraintOkWithFieldId(preconditionConstraintIsOk,
      startPosition1,
      startPosition1,
      (uint64_t)1U);
  if (EverParseIsError(resultAfterPrecondition))
  {
    return resultAfterPrecondition;
  }
  /* Field _boundedSum_left */
  uint32_t positionBeforeBoundedSum = *Input.pos;
  uint64_t resultAfterBoundedSum = ValidateBoundedSumLeft(Ctxt, Err, Input);
  uint64_t resultAfterleft;
  if (EverParseIsSuccess(resultAfterBoundedSum))
  {
    resultAfterleft = resultAfterBoundedSum;
  }
  else
  {
    Err("_boundedSum",
      "left",
      EverParseErrorReasonOfResult(resultAfterBoundedSum),
      Ctxt,
      Input,
      positionBeforeBoundedSum);
    resultAfterleft = resultAfterBoundedSum;
  }
  if (EverParseIsError(resultAfterleft))
  {
    return resultAfterleft;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition = *Input.pos;
  uint8_t *res = Input.buf + currentPosition;
  *Input.pos = currentPosition + (uint32_t)4U;
  uint8_t *temp1 = res;
  uint32_t res0 = Load32Le(temp1);
  uint32_t left = res0;
  /* Field _boundedSum_right */
  uint32_t positionBeforeBoundedSum0 = *Input.pos;
  uint64_t resultAfterBoundedSum0 = ValidateBoundedSumRight(Bound, left, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterBoundedSum0))
  {
    return resultAfterBoundedSum0;
  }
  Err("_boundedSum",
    "right",
    EverParseErrorReasonOfResult(resultAfterBoundedSum0),
    Ctxt,
    Input,
    positionBeforeBoundedSum0);
  return resultAfterBoundedSum0;
}

