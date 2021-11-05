

#include "Smoker.h"

static inline uint64_t
ValidateSmokerCigarettesConsumed(
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
/*++
    Internal helper function:
        Validator for field _smoker_cigarettesConsumed
        of type Smoker._smoker
--*/
{
  /* Validating field cigarettesConsumed */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint64_t)1U <= (InputLength - StartPosition);
  uint64_t positionAfterSmoker;
  if (hasBytes)
  {
    positionAfterSmoker = StartPosition + (uint64_t)1U;
  }
  else
  {
    positionAfterSmoker =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterSmoker))
  {
    return positionAfterSmoker;
  }
  Err("_smoker",
    "_smoker_cigarettesConsumed",
    EverParseErrorReasonOfResult(positionAfterSmoker),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterSmoker;
}

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
  /* Validating field age */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterSmoker;
  if (hasBytes)
  {
    positionAfterSmoker = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterSmoker =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterage;
  if (EverParseIsSuccess(positionAfterSmoker))
  {
    positionAfterage = positionAfterSmoker;
  }
  else
  {
    Err("_smoker",
      "age",
      EverParseErrorReasonOfResult(positionAfterSmoker),
      Ctxt,
      Input,
      StartPosition);
    positionAfterage = positionAfterSmoker;
  }
  if (EverParseIsError(positionAfterage))
  {
    return positionAfterage;
  }
  uint8_t temp[4U] = { 0U };
  uint8_t *temp1 = Input + (uint32_t)StartPosition;
  uint32_t res = Load32Le(temp1);
  uint32_t age = res;
  BOOLEAN ageConstraintIsOk = age >= (uint32_t)(uint8_t)21U;
  uint64_t positionAfterage1 = EverParseCheckConstraintOk(ageConstraintIsOk, positionAfterage);
  if (EverParseIsError(positionAfterage1))
  {
    return positionAfterage1;
  }
  /* Field _smoker_cigarettesConsumed */
  uint64_t
  positionAfterSmoker0 =
    ValidateSmokerCigarettesConsumed(Ctxt,
      Err,
      Input,
      InputLength,
      positionAfterage1);
  if (EverParseIsSuccess(positionAfterSmoker0))
  {
    return positionAfterSmoker0;
  }
  Err("_smoker",
    "cigarettesConsumed",
    EverParseErrorReasonOfResult(positionAfterSmoker0),
    Ctxt,
    Input,
    positionAfterage1);
  return positionAfterSmoker0;
}

