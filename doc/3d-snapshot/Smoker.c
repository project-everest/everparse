

#include "Smoker.h"

/*
Auto-generated field identifier for error reporting
*/
#define SMOKER__AGE ((uint64_t)1U)

/*
Auto-generated field identifier for error reporting
*/
#define SMOKER__CIGARETTESCONSUMED ((uint64_t)2U)

static inline uint64_t
ValidateSmokerCigarettesConsumed(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _smoker_cigarettesConsumed
        of type _smoker
--*/
{
  /* Validating field cigarettesConsumed */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint64_t endPositionOrError;
  if (((uint64_t)Input.len - StartPosition) < (uint64_t)1U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)1U;
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      SMOKER__CIGARETTESCONSUMED);
}

uint64_t SmokerValidateSmoker(InputBuffer Input, uint64_t StartPosition)
{
  /* Validating field age */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)Input.len - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  uint64_t
  positionAfterage = EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, SMOKER__AGE);
  if (EverParseIsError(positionAfterage))
  {
    return positionAfterage;
  }
  uint32_t age = Load32Le(Input.base + (uint32_t)StartPosition);
  BOOLEAN ageConstraintIsOk = age >= (uint32_t)(uint8_t)21U;
  uint64_t
  positionOrErrorAfterage =
    EverParseCheckConstraintOkWithFieldId(ageConstraintIsOk,
      StartPosition,
      positionAfterage,
      SMOKER__AGE);
  if (EverParseIsError(positionOrErrorAfterage))
  {
    return positionOrErrorAfterage;
  }
  /* Field _smoker_cigarettesConsumed */
  return ValidateSmokerCigarettesConsumed(Input, positionOrErrorAfterage);
}

