

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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterAge0;
  uint64_t positionAfterAge;
  uint32_t age;
  BOOLEAN ageConstraintIsOk;
  uint64_t positionAfterCheckedAge;
  BOOLEAN hasBytes;
  uint64_t positionAfterCigarettesConsumed;
  uint64_t res;
  if (hasBytes0)
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
      hasBytes = (InputLength - positionAfterCheckedAge) >= 1ULL;
      if (hasBytes)
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
        res = positionAfterCigarettesConsumed;
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
        res = positionAfterCigarettesConsumed;
      }
      positionAfterAge = res;
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

