

#include "BoundedSumConst.h"

/*
Auto-generated field identifier for error reporting
*/
#define BOUNDEDSUMCONST__BOUNDEDSUM__LEFT ((uint64_t)14U)

/*
Auto-generated field identifier for error reporting
*/
#define BOUNDEDSUMCONST__BOUNDEDSUM__RIGHT ((uint64_t)15U)

static inline uint64_t ValidateBoundedSumLeft(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _boundedSum_left
        of type BoundedSumConst._boundedSum
--*/
{
  /* SNIPPET_START: boundedSumCorrect */
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
      BOUNDEDSUMCONST__BOUNDEDSUM__LEFT);
}

static inline uint64_t
ValidateBoundedSumRight(
  uint32_t Left,
  uint32_t InputLength,
  uint8_t *Input,
  uint64_t StartPosition
)
/*++
    Internal helper function:
        Validator for field _boundedSum_right
        of type BoundedSumConst._boundedSum
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
    BOOLEAN
    boundedSumRightConstraintIsOk =
      Left
      <= (uint32_t)(uint8_t)42U
      && boundedSumRight <= ((uint32_t)(uint8_t)42U - Left);
    /* end: checking constraint */
    endPositionOrError =
      EverParseCheckConstraintOk(boundedSumRightConstraintIsOk,
        positionAfterBoundedSumRight);
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      BOUNDEDSUMCONST__BOUNDEDSUM__RIGHT);
}

uint64_t
BoundedSumConstValidateBoundedSum(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
 The following will fail because of integer overflow
// SNIPPET_START: boundedSumNaive
entrypoint typedef struct _boundedSum {
  UINT32 left;
  UINT32 right { left + right <= 42 };
} boundedSum;
// SNIPPET_END: boundedSumNaive

--*/
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
  return ValidateBoundedSumRight(left, InputLength, Input, positionAfterleft);
}

