

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
  uint64_t positionAfterAge0;
  uint64_t positionAfterAge;
  uint32_t age;
  BOOLEAN ageConstraintIsOk;
  uint64_t positionAfterCheckedAge;
  BOOLEAN hasBytesForCigarettesConsumed;
  uint64_t positionAfterCigarettesConsumed;
  uint64_t resForAge;
  if (hasBytesForAge)
  {
    positionAfterAge0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterAge0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterAge0))
  {
    positionAfterAge = positionAfterAge0;
  }
  else
  {
    age = Load32Le(Input + (uint32_t)StartPosition);
    ageConstraintIsOk = age >= 21U;
    positionAfterCheckedAge = EverParseCheckConstraintOk(ageConstraintIsOk, positionAfterAge0);
    if (EverParseIsError(positionAfterCheckedAge))
    {
      positionAfterAge = positionAfterCheckedAge;
    }
    else
    {
      /* Validating field cigarettesConsumed */
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      hasBytesForCigarettesConsumed = (InputLength - positionAfterCheckedAge) >= 1ULL;
      if (hasBytesForCigarettesConsumed)
      {
        positionAfterCigarettesConsumed = positionAfterCheckedAge + 1ULL;
      }
      else
      {
        positionAfterCigarettesConsumed =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedAge);
      }
      if (EverParseIsSuccess(positionAfterCigarettesConsumed))
      {
        resForAge = positionAfterCigarettesConsumed;
      }
      else
      {
        ErrorHandlerFn("_smoker",
          "cigarettesConsumed",
          EverParseErrorReasonOfResult(positionAfterCigarettesConsumed),
          EverParseGetValidatorErrorKind(positionAfterCigarettesConsumed),
          Ctxt,
          Input,
          positionAfterCheckedAge);
        resForAge = positionAfterCigarettesConsumed;
      }
      positionAfterAge = resForAge;
    }
  }
  if (EverParseIsSuccess(positionAfterAge))
  {
    return positionAfterAge;
  }
  ErrorHandlerFn("_smoker",
    "age",
    EverParseErrorReasonOfResult(positionAfterAge),
    EverParseGetValidatorErrorKind(positionAfterAge),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterAge;
}

