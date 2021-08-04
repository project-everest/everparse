

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
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _orderedPair_lesser
        of type OrderedPair._orderedPair
--*/
{
  /* Validating field lesser */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)(uint32_t)4U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterOrderedPair;
  if (hasBytes)
  {
    positionAfterOrderedPair = Pos + (uint64_t)(uint32_t)4U;
  }
  else
  {
    positionAfterOrderedPair =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterOrderedPair))
  {
    return positionAfterOrderedPair;
  }
  Err("_orderedPair",
    "_orderedPair_lesser",
    EverParseErrorReasonOfResult(positionAfterOrderedPair),
    Ctxt,
    Input,
    Pos);
  return positionAfterOrderedPair;
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
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _orderedPair_greater
        of type OrderedPair._orderedPair
--*/
{
  /* Validating field greater */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)(uint32_t)4U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterOrderedPair;
  if (hasBytes)
  {
    positionAfterOrderedPair = Pos + (uint64_t)(uint32_t)4U;
  }
  else
  {
    positionAfterOrderedPair =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  uint64_t positionAfterOrderedPair0;
  if (EverParseIsSuccess(positionAfterOrderedPair))
  {
    positionAfterOrderedPair0 = positionAfterOrderedPair;
  }
  else
  {
    Err("_orderedPair",
      "_orderedPair_greater",
      EverParseErrorReasonOfResult(positionAfterOrderedPair),
      Ctxt,
      Input,
      Pos);
    positionAfterOrderedPair0 = positionAfterOrderedPair;
  }
  uint64_t positionAfterOrderedPair1;
  if (EverParseIsError(positionAfterOrderedPair0))
  {
    positionAfterOrderedPair1 = positionAfterOrderedPair0;
  }
  else
  {
    /* reading field value */
    uint8_t temp[4U] = { 0U };
    uint8_t *temp1 = Input.buf + (uint32_t)Pos;
    uint32_t res = Load32Le(temp1);
    uint32_t orderedPair1 = res;
    /* start: checking constraint */
    BOOLEAN orderedPairConstraintIsOk = Lesser <= orderedPair1;
    /* end: checking constraint */
    positionAfterOrderedPair1 =
      EverParseCheckConstraintOk(orderedPairConstraintIsOk,
        positionAfterOrderedPair0);
  }
  if (EverParseIsSuccess(positionAfterOrderedPair1))
  {
    return positionAfterOrderedPair1;
  }
  Err("_orderedPair",
    "_orderedPair_greater.refinement",
    EverParseErrorReasonOfResult(positionAfterOrderedPair1),
    Ctxt,
    Input,
    Pos);
  return positionAfterOrderedPair1;
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
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
{
  /* Field _orderedPair_lesser */
  uint64_t positionAfterOrderedPair = ValidateOrderedPairLesser(Ctxt, Err, Input, Pos);
  uint64_t positionAfterlesser;
  if (EverParseIsSuccess(positionAfterOrderedPair))
  {
    positionAfterlesser = positionAfterOrderedPair;
  }
  else
  {
    Err("_orderedPair",
      "lesser",
      EverParseErrorReasonOfResult(positionAfterOrderedPair),
      Ctxt,
      Input,
      Pos);
    positionAfterlesser = positionAfterOrderedPair;
  }
  if (EverParseIsError(positionAfterlesser))
  {
    return positionAfterlesser;
  }
  uint8_t temp[4U] = { 0U };
  uint8_t *temp1 = Input.buf + (uint32_t)Pos;
  uint32_t res = Load32Le(temp1);
  uint32_t lesser = res;
  /* Field _orderedPair_greater */
  uint64_t
  positionAfterOrderedPair0 =
    ValidateOrderedPairGreater(lesser,
      Ctxt,
      Err,
      Input,
      positionAfterlesser);
  if (EverParseIsSuccess(positionAfterOrderedPair0))
  {
    return positionAfterOrderedPair0;
  }
  Err("_orderedPair",
    "greater",
    EverParseErrorReasonOfResult(positionAfterOrderedPair0),
    Ctxt,
    Input,
    positionAfterlesser);
  return positionAfterOrderedPair0;
}

