

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

static inline uint64_t ValidateBoundedSumLeft(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _boundedSum_left
        of type BoundedSum._boundedSum
--*/
{
  /* SNIPPET_START: boundedSum */
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
      BOUNDEDSUM__BOUNDEDSUM__LEFT);
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
        of type BoundedSum._boundedSum
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
      BOUNDEDSUM__BOUNDEDSUM__RIGHT);
}

uint64_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
  uint32_t InputLength,
  uint8_t *Input,
  uint64_t StartPosition
)
{
  /* Field _boundedSum_left */
  uint64_t positionAfterleft = ValidateBoundedSumLeft(InputLength, StartPosition);
  if (EverParseIsError(positionAfterleft))
  {
    return positionAfterleft;
  }
  uint8_t *base = Input;
  uint32_t left = Load32Le(base + (uint32_t)StartPosition);
  /* Field _boundedSum_right */
  return ValidateBoundedSumRight(Bound, left, InputLength, Input, positionAfterleft);
}

static inline uint64_t ValidateMySumBound(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field mySum_bound
        of type BoundedSum.mySum
--*/
{
  /* Validating field bound */
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
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, BOUNDEDSUM_MYSUM__BOUND);
}

static inline uint64_t
ValidateMySumSum(uint32_t Bound, uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field mySum_sum
        of type BoundedSum.mySum
--*/
{
  /* Validating field sum */
  return BoundedSumValidateBoundedSum(Bound, InputLength, Input, StartPosition);
}

uint64_t BoundedSumValidateMySum(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Field mySum_bound */
  uint64_t positionAfterbound = ValidateMySumBound(InputLength, StartPosition);
  if (EverParseIsError(positionAfterbound))
  {
    return positionAfterbound;
  }
  uint8_t *base = Input;
  uint32_t bound = Load32Le(base + (uint32_t)StartPosition);
  /* Field mySum_sum */
  return ValidateMySumSum(bound, InputLength, Input, positionAfterbound);
}

