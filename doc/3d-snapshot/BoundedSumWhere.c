

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

static inline uint64_t ValidateBoundedSumLeft(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _boundedSum_left
        of type BoundedSumWhere._boundedSum
--*/
{
  /* Validating field left */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      BOUNDEDSUMWHERE__BOUNDEDSUM__LEFT);
}

static inline uint64_t
ValidateBoundedSumRight(
  uint32_t Bound,
  uint32_t Left,
  uint32_t InputLength,
  uint8_t *Input,
  uint64_t StartPosition
)
/*++
    Internal helper function:
        Validator for field _boundedSum_right
        of type BoundedSumWhere._boundedSum
--*/
{
  /* Validating field right */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterBoundedSumRight;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    positionAfterBoundedSumRight = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterBoundedSumRight = StartPosition + (uint64_t)4U;
  }
  uint64_t endPositionOrError;
  if (EverParseIsError(positionAfterBoundedSumRight))
  {
    endPositionOrError = positionAfterBoundedSumRight;
  }
  else
  {
    /* reading field value */
    uint8_t *base = Input;
    uint32_t boundedSumRight = Load32Le(base + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN boundedSumRightConstraintIsOk = Left <= Bound && boundedSumRight <= (Bound - Left);
    /* end: checking constraint */
    endPositionOrError =
      EverParseCheckConstraintOk(boundedSumRightConstraintIsOk,
        positionAfterBoundedSumRight);
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      BOUNDEDSUMWHERE__BOUNDEDSUM__RIGHT);
}

uint64_t
BoundedSumWhereValidateBoundedSum(
  uint32_t Bound,
  uint32_t InputLength,
  uint8_t *Input,
  uint64_t StartPosition
)
{
  /* Validating field __precondition */
  BOOLEAN preconditionConstraintIsOk = Bound <= (uint32_t)(uint16_t)1729U;
  uint64_t
  positionOrErrorAfterPrecondition =
    EverParseCheckConstraintOkWithFieldId(preconditionConstraintIsOk,
      StartPosition,
      StartPosition,
      BOUNDEDSUMWHERE__BOUNDEDSUM____PRECONDITION);
  if (EverParseIsError(positionOrErrorAfterPrecondition))
  {
    return positionOrErrorAfterPrecondition;
  }
  /* Field _boundedSum_left */
  uint64_t
  positionAfterleft = ValidateBoundedSumLeft(InputLength, positionOrErrorAfterPrecondition);
  if (EverParseIsError(positionAfterleft))
  {
    return positionAfterleft;
  }
  uint8_t *base = Input;
  uint32_t left = Load32Le(base + (uint32_t)positionOrErrorAfterPrecondition);
  /* Field _boundedSum_right */
  return ValidateBoundedSumRight(Bound, left, InputLength, Input, positionAfterleft);
}

