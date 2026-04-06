

#include "Smoker.h"

uint64_t
SmokerValidateSmoker(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterage;
  uint64_t positionAfterSmoker;
  uint32_t age;
  BOOLEAN ageConstraintIsOk;
  uint64_t positionAfterage1;
  BOOLEAN hasBytes;
  uint64_t positionAfterSmoker0;
  uint64_t res;
  if (hasBytes0)
  {
    positionAfterage = StartPosition + 4ULL;
  }
  else
  {
    positionAfterage =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterage))
  {
    positionAfterSmoker = positionAfterage;
  }
  else
  {
    age = Load32Le(Input + (uint32_t)StartPosition);
    ageConstraintIsOk = age >= (uint32_t)21U;
    positionAfterage1 = EverParseCheckConstraintOk(ageConstraintIsOk, positionAfterage);
    if (EverParseIsError(positionAfterage1))
    {
      positionAfterSmoker = positionAfterage1;
    }
    else
    {
      /* Validating field cigarettesConsumed */
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      hasBytes = 1ULL <= (InputLength - positionAfterage1);
      if (hasBytes)
      {
        positionAfterSmoker0 = positionAfterage1 + 1ULL;
      }
      else
      {
        positionAfterSmoker0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterage1);
      }
      if (EverParseIsSuccess(positionAfterSmoker0))
      {
        res = positionAfterSmoker0;
      }
      else
      {
        ErrorHandlerFn("_smoker",
          "cigarettesConsumed",
          EverParseErrorReasonOfResult(positionAfterSmoker0),
          EverParseGetValidatorErrorKind(positionAfterSmoker0),
          Ctxt,
          Input,
          positionAfterage1);
        res = positionAfterSmoker0;
      }
      positionAfterSmoker = res;
    }
  }
  if (EverParseIsSuccess(positionAfterSmoker))
  {
    return positionAfterSmoker;
  }
  ErrorHandlerFn("_smoker",
    "age",
    EverParseErrorReasonOfResult(positionAfterSmoker),
    EverParseGetValidatorErrorKind(positionAfterSmoker),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterSmoker;
}

