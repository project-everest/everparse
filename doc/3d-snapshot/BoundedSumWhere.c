

#include "BoundedSumWhere.h"

/*
Auto-generated field identifier for error reporting
*/
#define BOUNDEDSUMWHERE__BOUNDEDSUM____PRECONDITION ((uint64_t)16U)

/*
Auto-generated field identifier for error reporting
*/
#define BOUNDEDSUMWHERE__BOUNDEDSUM__LEFT ((uint64_t)17U)

/*
Auto-generated field identifier for error reporting
*/
#define BOUNDEDSUMWHERE__BOUNDEDSUM__RIGHT ((uint64_t)18U)

static inline uint64_t ValidateBoundedSumLeft(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _boundedSum_left
        of type BoundedSumWhere._boundedSum
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field left */
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
  return EverParseMaybeSetErrorCode(result, startPosition1, BOUNDEDSUMWHERE__BOUNDEDSUM__LEFT);
}

static inline uint64_t
ValidateBoundedSumRight(uint32_t Bound, uint32_t Left, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _boundedSum_right
        of type BoundedSumWhere._boundedSum
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
  return EverParseMaybeSetErrorCode(result, startPosition1, BOUNDEDSUMWHERE__BOUNDEDSUM__RIGHT);
}

uint64_t BoundedSumWhereValidateBoundedSum(uint32_t Bound, EverParseInputBuffer Input)
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
      BOUNDEDSUMWHERE__BOUNDEDSUM____PRECONDITION);
  if (EverParseIsError(resultAfterPrecondition))
  {
    return resultAfterPrecondition;
  }
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

