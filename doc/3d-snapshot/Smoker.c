

#include "Smoker.h"

#include "EverParse.h"

uint64_t
SmokerValidateSmoker(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytesForAge = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterAge;
  uint64_t positionAfterAgeOrError;
  uint32_t age;
  BOOLEAN ageConstraintIsOk;
  uint64_t positionAfterCheckedAge;
  BOOLEAN hasBytesForCigarettesConsumed;
  uint64_t positionAfterCigarettesConsumedOrError;
  uint64_t resForAge;
  if (hasBytesForAge)
  {
    positionAfterAge = StartPosition + 4ULL;
  }
  else
  {
    positionAfterAge =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterAge))
  {
    positionAfterAgeOrError = positionAfterAge;
  }
  else
  {
    age = Load32Le(Input + (uint32_t)StartPosition);
    ageConstraintIsOk = age >= 21U;
    positionAfterCheckedAge = EverParseCheckConstraintOk(ageConstraintIsOk, positionAfterAge);
    if (EverParseIsError(positionAfterCheckedAge))
    {
      positionAfterAgeOrError = positionAfterCheckedAge;
    }
    else
    {
      /* Validating field cigarettesConsumed */
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      hasBytesForCigarettesConsumed = (InputLength - positionAfterCheckedAge) >= 1ULL;
      if (hasBytesForCigarettesConsumed)
      {
        positionAfterCigarettesConsumedOrError = positionAfterCheckedAge + 1ULL;
      }
      else
      {
        positionAfterCigarettesConsumedOrError =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedAge);
      }
      if (EverParseIsSuccess(positionAfterCigarettesConsumedOrError))
      {
        resForAge = positionAfterCigarettesConsumedOrError;
      }
      else
      {
        ErrorHandlerFn("_smoker",
          "cigarettesConsumed",
          EverParseErrorReasonOfResult(positionAfterCigarettesConsumedOrError),
          EverParseGetValidatorErrorKind(positionAfterCigarettesConsumedOrError),
          Ctxt,
          Input,
          positionAfterCheckedAge);
        resForAge = positionAfterCigarettesConsumedOrError;
      }
      positionAfterAgeOrError = resForAge;
    }
  }
  if (EverParseIsSuccess(positionAfterAgeOrError))
  {
    return positionAfterAgeOrError;
  }
  ErrorHandlerFn("_smoker",
    "age",
    EverParseErrorReasonOfResult(positionAfterAgeOrError),
    EverParseGetValidatorErrorKind(positionAfterAgeOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterAgeOrError;
}

