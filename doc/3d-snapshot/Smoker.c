

#include "Smoker.h"

/*
Auto-generated field identifier for error reporting
*/
#define SMOKER__SMOKER__AGE ((uint64_t)37U)

/*
Auto-generated field identifier for error reporting
*/
#define SMOKER__SMOKER__CIGARETTESCONSUMED ((uint64_t)38U)

static inline uint64_t
ValidateSmokerCigarettesConsumed(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _smoker_cigarettesConsumed
        of type Smoker._smoker
--*/
{
  /* Validating field cigarettesConsumed */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)1U)
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
      SMOKER__SMOKER__CIGARETTESCONSUMED);
}

uint64_t SmokerValidateSmoker(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Validating field age */
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
  uint64_t
  positionAfterage =
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      SMOKER__SMOKER__AGE);
  if (EverParseIsError(positionAfterage))
  {
    return positionAfterage;
  }
  uint8_t *base = Input;
  uint32_t age = Load32Le(base + (uint32_t)StartPosition);
  BOOLEAN ageConstraintIsOk = age >= (uint32_t)(uint8_t)21U;
  uint64_t
  positionOrErrorAfterage =
    EverParseCheckConstraintOkWithFieldId(ageConstraintIsOk,
      StartPosition,
      positionAfterage,
      SMOKER__SMOKER__AGE);
  if (EverParseIsError(positionOrErrorAfterage))
  {
    return positionOrErrorAfterage;
  }
  /* Field _smoker_cigarettesConsumed */
  return ValidateSmokerCigarettesConsumed(InputLength, positionOrErrorAfterage);
}

