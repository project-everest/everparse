

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
  uint64_t positionAfterage0;
  uint64_t positionAfterage;
  uint32_t age;
  BOOLEAN ageConstraintIsOk;
  uint64_t positionAfterCheckedage;
  BOOLEAN hasBytes;
  uint64_t positionAftercigarettesConsumed;
  uint64_t res;
  if (hasBytes0)
  {
    positionAfterage0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterage0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterage0))
  {
    positionAfterage = positionAfterage0;
  }
  else
  {
    age = Load32Le(Input + (uint32_t)StartPosition);
    ageConstraintIsOk = age >= 21U;
    positionAfterCheckedage = EverParseCheckConstraintOk(ageConstraintIsOk, positionAfterage0);
    if (EverParseIsError(positionAfterCheckedage))
    {
      positionAfterage = positionAfterCheckedage;
    }
    else
    {
      /* Validating field cigarettesConsumed */
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      hasBytes = (InputLength - positionAfterCheckedage) >= 1ULL;
      if (hasBytes)
      {
        positionAftercigarettesConsumed = positionAfterCheckedage + 1ULL;
      }
      else
      {
        positionAftercigarettesConsumed =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedage);
      }
      if (EverParseIsSuccess(positionAftercigarettesConsumed))
      {
        res = positionAftercigarettesConsumed;
      }
      else
      {
        ErrorHandlerFn("_smoker",
          "cigarettesConsumed",
          EverParseErrorReasonOfResult(positionAftercigarettesConsumed),
          EverParseGetValidatorErrorKind(positionAftercigarettesConsumed),
          Ctxt,
          Input,
          positionAfterCheckedage);
        res = positionAftercigarettesConsumed;
      }
      positionAfterage = res;
    }
  }
  if (EverParseIsSuccess(positionAfterage))
  {
    return positionAfterage;
  }
  ErrorHandlerFn("_smoker",
    "age",
    EverParseErrorReasonOfResult(positionAfterage),
    EverParseGetValidatorErrorKind(positionAfterage),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterage;
}

