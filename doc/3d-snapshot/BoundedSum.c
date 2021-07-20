

#include "BoundedSum.h"

/*
Auto-generated field identifier for error reporting
*/
#define BOUNDEDSUM__BOUNDEDSUM__LEFT ((uint64_t)11U)

/*
Auto-generated field identifier for error reporting
*/
#define BOUNDEDSUM__BOUNDEDSUM__RIGHT ((uint64_t)12U)

/*
Auto-generated field identifier for error reporting
*/
#define BOUNDEDSUM_MYSUM__BOUND ((uint64_t)13U)

static inline uint64_t ValidateBoundedSumLeft(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _boundedSum_left
        of type BoundedSum._boundedSum
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* SNIPPET_START: boundedSum */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, BOUNDEDSUM__BOUNDEDSUM__LEFT);
}

static inline uint64_t
ValidateBoundedSumRight(uint32_t Bound, uint32_t Left, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _boundedSum_right
        of type BoundedSum._boundedSum
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field right */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition0 = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition0);
  uint64_t resultAfterBoundedSumRight;
  if (hasBytes)
  {
    resultAfterBoundedSumRight = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterBoundedSumRight = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t result;
  if (EverParseIsError(resultAfterBoundedSumRight))
  {
    result = resultAfterBoundedSumRight;
  }
  else
  {
    /* reading field value */
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    memcpy(temp, Input.buf + currentPosition, (uint32_t)4U * sizeof (uint8_t));
    *Input.pos = currentPosition + (uint32_t)4U;
    uint32_t res = Load32Le(temp);
    uint32_t boundedSumRight = res;
    /* start: checking constraint */
    BOOLEAN boundedSumRightConstraintIsOk = Left <= Bound && boundedSumRight <= (Bound - Left);
    /* end: checking constraint */
    result = EverParseCheckConstraintOk(boundedSumRightConstraintIsOk, resultAfterBoundedSumRight);
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, BOUNDEDSUM__BOUNDEDSUM__RIGHT);
}

uint64_t BoundedSumValidateBoundedSum(uint32_t Bound, EverParseInputBuffer Input)
{
  /* Field _boundedSum_left */
  uint64_t resultAfterleft = ValidateBoundedSumLeft(Input);
  if (EverParseIsError(resultAfterleft))
  {
    return resultAfterleft;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition = *Input.pos;
  memcpy(temp, Input.buf + currentPosition, (uint32_t)4U * sizeof (uint8_t));
  *Input.pos = currentPosition + (uint32_t)4U;
  uint32_t res = Load32Le(temp);
  uint32_t left = res;
  /* Field _boundedSum_right */
  return ValidateBoundedSumRight(Bound, left, Input);
}

static inline uint64_t ValidateMySumBound(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field mySum_bound
        of type BoundedSum.mySum
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field bound */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, BOUNDEDSUM_MYSUM__BOUND);
}

static inline uint64_t ValidateMySumSum(uint32_t Bound, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field mySum_sum
        of type BoundedSum.mySum
--*/
{
  /* Validating field sum */
  return BoundedSumValidateBoundedSum(Bound, Input);
}

uint64_t BoundedSumValidateMySum(EverParseInputBuffer Input)
{
  /* Field mySum_bound */
  uint64_t resultAfterbound = ValidateMySumBound(Input);
  if (EverParseIsError(resultAfterbound))
  {
    return resultAfterbound;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition = *Input.pos;
  memcpy(temp, Input.buf + currentPosition, (uint32_t)4U * sizeof (uint8_t));
  *Input.pos = currentPosition + (uint32_t)4U;
  uint32_t res = Load32Le(temp);
  uint32_t bound = res;
  /* Field mySum_sum */
  return ValidateMySumSum(bound, Input);
}

