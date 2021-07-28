

#include "OrderedPair.h"

static inline uint64_t
ValidateOrderedPairLesser(
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
        Validator for field _orderedPair_lesser
        of type OrderedPair._orderedPair
--*/
{
  /* Validating field lesser */
  uint32_t positionBeforeOrderedPair = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterOrderedPair;
  if (hasBytes)
  {
    resultAfterOrderedPair = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterOrderedPair = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterOrderedPair))
  {
    return resultAfterOrderedPair;
  }
  Err("_orderedPair",
    "_orderedPair_lesser",
    EverParseErrorReasonOfResult(resultAfterOrderedPair),
    Ctxt,
    Input,
    positionBeforeOrderedPair);
  return resultAfterOrderedPair;
}

static inline uint64_t
ValidateOrderedPairGreater(
  uint32_t Lesser,
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
        Validator for field _orderedPair_greater
        of type OrderedPair._orderedPair
--*/
{
  /* Validating field greater */
  uint32_t positionBeforeOrderedPair = *Input.pos;
  uint32_t positionBeforeOrderedPair1 = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterOrderedPair;
  if (hasBytes)
  {
    resultAfterOrderedPair = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterOrderedPair = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  uint64_t resultAfterOrderedPair0;
  if (EverParseIsSuccess(resultAfterOrderedPair))
  {
    resultAfterOrderedPair0 = resultAfterOrderedPair;
  }
  else
  {
    Err("_orderedPair",
      "_orderedPair_greater",
      EverParseErrorReasonOfResult(resultAfterOrderedPair),
      Ctxt,
      Input,
      positionBeforeOrderedPair1);
    resultAfterOrderedPair0 = resultAfterOrderedPair;
  }
  uint64_t resultAfterOrderedPair1;
  if (EverParseIsError(resultAfterOrderedPair0))
  {
    resultAfterOrderedPair1 = resultAfterOrderedPair0;
  }
  else
  {
    /* reading field value */
    uint8_t temp[4U] = { 0U };
    uint32_t currentPosition = *Input.pos;
    uint8_t *res = Input.buf + currentPosition;
    *Input.pos = currentPosition + (uint32_t)4U;
    uint8_t *temp1 = res;
    uint32_t res0 = Load32Le(temp1);
    uint32_t orderedPair1 = res0;
    /* start: checking constraint */
    BOOLEAN orderedPairConstraintIsOk = Lesser <= orderedPair1;
    /* end: checking constraint */
    resultAfterOrderedPair1 =
      EverParseCheckConstraintOk(orderedPairConstraintIsOk,
        resultAfterOrderedPair0);
  }
  if (EverParseIsSuccess(resultAfterOrderedPair1))
  {
    return resultAfterOrderedPair1;
  }
  Err("_orderedPair",
    "_orderedPair_greater.refinement",
    EverParseErrorReasonOfResult(resultAfterOrderedPair1),
    Ctxt,
    Input,
    positionBeforeOrderedPair);
  return resultAfterOrderedPair1;
}

uint64_t
OrderedPairValidateOrderedPair(
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
  /* Field _orderedPair_lesser */
  uint32_t positionBeforeOrderedPair = *Input.pos;
  uint64_t resultAfterOrderedPair = ValidateOrderedPairLesser(Ctxt, Err, Input);
  uint64_t resultAfterlesser;
  if (EverParseIsSuccess(resultAfterOrderedPair))
  {
    resultAfterlesser = resultAfterOrderedPair;
  }
  else
  {
    Err("_orderedPair",
      "lesser",
      EverParseErrorReasonOfResult(resultAfterOrderedPair),
      Ctxt,
      Input,
      positionBeforeOrderedPair);
    resultAfterlesser = resultAfterOrderedPair;
  }
  if (EverParseIsError(resultAfterlesser))
  {
    return resultAfterlesser;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition = *Input.pos;
  uint8_t *res = Input.buf + currentPosition;
  *Input.pos = currentPosition + (uint32_t)4U;
  uint8_t *temp1 = res;
  uint32_t res0 = Load32Le(temp1);
  uint32_t lesser = res0;
  /* Field _orderedPair_greater */
  uint32_t positionBeforeOrderedPair0 = *Input.pos;
  uint64_t resultAfterOrderedPair0 = ValidateOrderedPairGreater(lesser, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterOrderedPair0))
  {
    return resultAfterOrderedPair0;
  }
  Err("_orderedPair",
    "greater",
    EverParseErrorReasonOfResult(resultAfterOrderedPair0),
    Ctxt,
    Input,
    positionBeforeOrderedPair0);
  return resultAfterOrderedPair0;
}

