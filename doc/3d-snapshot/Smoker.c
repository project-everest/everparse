

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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _smoker_cigarettesConsumed
        of type Smoker._smoker
--*/
{
  /* Validating field cigarettesConsumed */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - Pos);
  uint64_t positionAfterSmoker;
  if (hasBytes)
  {
    positionAfterSmoker = (uint64_t)(Pos + (uint32_t)1U);
  }
  else
  {
    positionAfterSmoker = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
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
    Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t StartPosition
)
{
  /* Validating field age */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - StartPosition);
  uint64_t positionAfterSmoker;
  if (hasBytes)
  {
    positionAfterSmoker = (uint64_t)(StartPosition + (uint32_t)4U);
  }
  else
  {
    positionAfterSmoker = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
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
  uint8_t *temp1 = Input.buf + StartPosition;
  uint32_t res0 = Load32Le(temp1);
  uint32_t age = res0;
  BOOLEAN ageConstraintIsOk = age >= (uint32_t)(uint8_t)21U;
  uint64_t
  positionAfterage1 =
    EverParseCheckConstraintOkWithFieldId(ageConstraintIsOk,
      (uint64_t)StartPosition,
      positionAfterage,
      (uint64_t)1U);
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
      (uint32_t)positionAfterage1);
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
      (uint32_t)positionAfterage1);
    res = positionAfterSmoker0;
  }
  if (EverParseIsSuccess(res))
  {
    
  }
  return res;
}

