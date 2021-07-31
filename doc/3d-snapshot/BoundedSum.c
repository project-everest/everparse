

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
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _boundedSum_left
        of type BoundedSum._boundedSum
--*/
{
  /* SNIPPET_START: boundedSum */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - Pos);
  uint64_t positionAfterBoundedSum;
  if (hasBytes)
  {
    positionAfterBoundedSum = (uint64_t)(Pos + (uint32_t)4U);
  }
  else
  {
    positionAfterBoundedSum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
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
    Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _boundedSum_right
        of type BoundedSum._boundedSum
--*/
{
  /* Validating field right */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - Pos);
  uint64_t positionAfterBoundedSum;
  if (hasBytes)
  {
    positionAfterBoundedSum = (uint64_t)(Pos + (uint32_t)4U);
  }
  else
  {
    positionAfterBoundedSum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
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
      Pos);
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
    uint8_t temp[4U] = { 0U };
    uint8_t *temp1 = Input.buf + Pos;
    uint32_t res = Load32Le(temp1);
    uint32_t boundedSum1 = res;
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
    Pos);
  return positionAfterBoundedSum1;
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
  EverParseInputBuffer Input,
  uint32_t Pos
)
{
  /* Field _boundedSum_left */
  uint64_t positionAfterBoundedSum = ValidateBoundedSumLeft(Ctxt, Err, Input, Pos);
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
      Pos);
    positionAfterleft = positionAfterBoundedSum;
  }
  if (EverParseIsError(positionAfterleft))
  {
    return positionAfterleft;
  }
  uint8_t temp[4U] = { 0U };
  uint8_t *temp1 = Input.buf + Pos;
  uint32_t res = Load32Le(temp1);
  uint32_t left = res;
  /* Field _boundedSum_right */
  uint64_t
  positionAfterBoundedSum0 =
    ValidateBoundedSumRight(Bound,
      left,
      Ctxt,
      Err,
      Input,
      (uint32_t)positionAfterleft);
  if (EverParseIsSuccess(positionAfterBoundedSum0))
  {
    return positionAfterBoundedSum0;
  }
  Err("_boundedSum",
    "right",
    EverParseErrorReasonOfResult(positionAfterBoundedSum0),
    Ctxt,
    Input,
    (uint32_t)positionAfterleft);
  return positionAfterBoundedSum0;
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
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field mySum_bound
        of type BoundedSum.mySum
--*/
{
  /* Validating field bound */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - Pos);
  uint64_t positionAftermySum;
  if (hasBytes)
  {
    positionAftermySum = (uint64_t)(Pos + (uint32_t)4U);
  }
  else
  {
    positionAftermySum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(positionAftermySum))
  {
    return positionAftermySum;
  }
  Err("mySum",
    "mySum_bound",
    EverParseErrorReasonOfResult(positionAftermySum),
    Ctxt,
    Input,
    Pos);
  return positionAftermySum;
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
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field mySum_sum
        of type BoundedSum.mySum
--*/
{
  /* Validating field sum */
  uint64_t positionAftermySum = BoundedSumValidateBoundedSum(Bound, Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAftermySum))
  {
    return positionAftermySum;
  }
  Err("mySum", "mySum_sum", EverParseErrorReasonOfResult(positionAftermySum), Ctxt, Input, Pos);
  return positionAftermySum;
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
  EverParseInputBuffer Input,
  uint32_t Pos
)
{
  /* Field mySum_bound */
  uint64_t positionAftermySum = ValidateMySumBound(Ctxt, Err, Input, Pos);
  uint64_t positionAfterbound;
  if (EverParseIsSuccess(positionAftermySum))
  {
    positionAfterbound = positionAftermySum;
  }
  else
  {
    Err("mySum", "bound", EverParseErrorReasonOfResult(positionAftermySum), Ctxt, Input, Pos);
    positionAfterbound = positionAftermySum;
  }
  if (EverParseIsError(positionAfterbound))
  {
    return positionAfterbound;
  }
  uint8_t temp[4U] = { 0U };
  uint8_t *temp1 = Input.buf + Pos;
  uint32_t res = Load32Le(temp1);
  uint32_t bound = res;
  /* Field mySum_sum */
  uint64_t
  positionAftermySum0 = ValidateMySumSum(bound, Ctxt, Err, Input, (uint32_t)positionAfterbound);
  if (EverParseIsSuccess(positionAftermySum0))
  {
    return positionAftermySum0;
  }
  Err("mySum",
    "sum",
    EverParseErrorReasonOfResult(positionAftermySum0),
    Ctxt,
    Input,
    (uint32_t)positionAfterbound);
  return positionAftermySum0;
}

