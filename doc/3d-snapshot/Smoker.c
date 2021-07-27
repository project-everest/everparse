

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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _smoker_cigarettesConsumed
        of type Smoker._smoker
--*/
{
  /* Validating field cigarettesConsumed */
  uint32_t positionBeforeSmoker = *Input.pos;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - currentPosition);
  uint64_t resultAfterSmoker;
  if (hasBytes)
  {
    resultAfterSmoker = (uint64_t)(uint32_t)1U;
  }
  else
  {
    resultAfterSmoker = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterSmoker))
  {
    return resultAfterSmoker;
  }
  Err("_smoker",
    "_smoker_cigarettesConsumed",
    EverParseErrorReasonOfResult(resultAfterSmoker),
    Ctxt,
    Input,
    positionBeforeSmoker);
  return resultAfterSmoker;
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
  EverParseInputBuffer Input
)
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field age */
  uint32_t positionBeforeSmoker = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition0 = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition0);
  uint64_t resultAfterSmoker;
  if (hasBytes)
  {
    resultAfterSmoker = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterSmoker = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t resultAfterage;
  if (EverParseIsSuccess(resultAfterSmoker))
  {
    resultAfterage = resultAfterSmoker;
  }
  else
  {
    Err("_smoker",
      "age",
      EverParseErrorReasonOfResult(resultAfterSmoker),
      Ctxt,
      Input,
      positionBeforeSmoker);
    resultAfterage = resultAfterSmoker;
  }
  if (EverParseIsError(resultAfterage))
  {
    return resultAfterage;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition1 = *Input.pos;
  uint8_t *res0 = Input.buf + currentPosition1;
  *Input.pos = currentPosition1 + (uint32_t)4U;
  uint8_t *temp1 = res0;
  uint32_t res1 = Load32Le(temp1);
  uint32_t age = res1;
  BOOLEAN ageConstraintIsOk = age >= (uint32_t)(uint8_t)21U;
  uint64_t
  resultAfterage1 =
    EverParseCheckConstraintOkWithFieldId(ageConstraintIsOk,
      startPosition1,
      resultAfterage,
      (uint64_t)1U);
  if (EverParseIsError(resultAfterage1))
  {
    return resultAfterage1;
  }
  /* Field _smoker_cigarettesConsumed */
  uint32_t positionBeforeSmoker0 = *Input.pos;
  uint64_t resultAfterSmoker0 = ValidateSmokerCigarettesConsumed(Ctxt, Err, Input);
  uint64_t res;
  if (EverParseIsSuccess(resultAfterSmoker0))
  {
    res = resultAfterSmoker0;
  }
  else
  {
    Err("_smoker",
      "cigarettesConsumed",
      EverParseErrorReasonOfResult(resultAfterSmoker0),
      Ctxt,
      Input,
      positionBeforeSmoker0);
    res = resultAfterSmoker0;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

