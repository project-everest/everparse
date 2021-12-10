

#include "Smoker.h"

uint64_t
SmokerValidateSmoker(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfternone;
  if (hasBytes0)
  {
    positionAfternone = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfternone =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterSmoker;
  if (EverParseIsError(positionAfternone))
  {
    positionAfterSmoker = positionAfternone;
  }
  else
  {
    uint32_t none = Load32Le(Input + (uint32_t)StartPosition);
    BOOLEAN noneConstraintIsOk = none >= (uint32_t)(uint8_t)21U;
    uint64_t
    positionAfternone1 = EverParseCheckConstraintOk(noneConstraintIsOk, positionAfternone);
    if (EverParseIsError(positionAfternone1))
    {
      positionAfterSmoker = positionAfternone1;
    }
    else
    {
      /* Validating field cigarettesConsumed */
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      BOOLEAN hasBytes = (uint64_t)1U <= (InputLength - positionAfternone1);
      uint64_t positionAfterSmoker0;
      if (hasBytes)
      {
        positionAfterSmoker0 = positionAfternone1 + (uint64_t)1U;
      }
      else
      {
        positionAfterSmoker0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfternone1);
      }
      uint64_t res;
      if (EverParseIsSuccess(positionAfterSmoker0))
      {
        res = positionAfterSmoker0;
      }
      else
      {
        Err("_smoker",
          "cigarettesConsumed",
          EverParseErrorReasonOfResult(positionAfterSmoker0),
          Ctxt,
          Input,
          positionAfternone1);
        res = positionAfterSmoker0;
      }
      positionAfterSmoker = res;
    }
  }
  if (EverParseIsSuccess(positionAfterSmoker))
  {
    return positionAfterSmoker;
  }
  Err("_smoker",
    "none",
    EverParseErrorReasonOfResult(positionAfterSmoker),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterSmoker;
}

