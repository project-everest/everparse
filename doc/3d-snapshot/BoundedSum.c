

#include "BoundedSum.h"

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
        of type BoundedSum._boundedSum
--*/
{
  /* SNIPPET_START: boundedSum */
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
        of type BoundedSum._boundedSum
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
BoundedSumValidateBoundedSum(
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

static inline uint64_t
ValidateMySumBound(
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
        Validator for field mySum_bound
        of type BoundedSum.mySum
--*/
{
  /* Validating field bound */
  uint32_t positionBeforemySum = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAftermySum;
  if (hasBytes)
  {
    resultAftermySum = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAftermySum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAftermySum))
  {
    return resultAftermySum;
  }
  Err("mySum",
    "mySum_bound",
    EverParseErrorReasonOfResult(resultAftermySum),
    Ctxt,
    Input,
    positionBeforemySum);
  return resultAftermySum;
}

static inline uint64_t
ValidateMySumSum(
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
/*++
    Internal helper function:
        Validator for field mySum_sum
        of type BoundedSum.mySum
--*/
{
  /* Validating field sum */
  uint32_t positionBeforemySum = *Input.pos;
  uint64_t resultAftermySum = BoundedSumValidateBoundedSum(Bound, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAftermySum))
  {
    return resultAftermySum;
  }
  Err("mySum",
    "mySum_sum",
    EverParseErrorReasonOfResult(resultAftermySum),
    Ctxt,
    Input,
    positionBeforemySum);
  return resultAftermySum;
}

uint64_t
BoundedSumValidateMySum(
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
  /* Field mySum_bound */
  uint32_t positionBeforemySum0 = *Input.pos;
  uint64_t resultAftermySum0 = ValidateMySumBound(Ctxt, Err, Input);
  uint64_t resultAfterbound;
  if (EverParseIsSuccess(resultAftermySum0))
  {
    resultAfterbound = resultAftermySum0;
  }
  else
  {
    Err("mySum",
      "bound",
      EverParseErrorReasonOfResult(resultAftermySum0),
      Ctxt,
      Input,
      positionBeforemySum0);
    resultAfterbound = resultAftermySum0;
  }
  if (EverParseIsError(resultAfterbound))
  {
    return resultAfterbound;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition = *Input.pos;
  uint8_t *res = Input.buf + currentPosition;
  *Input.pos = currentPosition + (uint32_t)4U;
  uint8_t *temp1 = res;
  uint32_t res0 = Load32Le(temp1);
  uint32_t bound = res0;
  /* Field mySum_sum */
  uint32_t positionBeforemySum = *Input.pos;
  uint64_t resultAftermySum = ValidateMySumSum(bound, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAftermySum))
  {
    return resultAftermySum;
  }
  Err("mySum",
    "sum",
    EverParseErrorReasonOfResult(resultAftermySum),
    Ctxt,
    Input,
    positionBeforemySum);
  return resultAftermySum;
}

