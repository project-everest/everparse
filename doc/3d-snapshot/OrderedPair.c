

#include "OrderedPair.h"



uint64_t
OrderedPairValidateOrderedPair(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
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
  BOOLEAN hasBytes0 = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterOrderedPair;
  if (hasBytes0)
  {
    positionAfterOrderedPair = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterOrderedPair =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterlesser;
  if (EverParseIsSuccess(positionAfterOrderedPair))
  {
    positionAfterlesser = positionAfterOrderedPair;
  }
  else
  {
    ErrorHandlerFn("_orderedPair",
      "lesser",
      EverParseErrorReasonOfResult(positionAfterOrderedPair),
      EverParseGetValidatorErrorKind(positionAfterOrderedPair),
      Ctxt,
      Input,
      StartPosition);
    positionAfterlesser = positionAfterOrderedPair;
  }
  if (EverParseIsError(positionAfterlesser))
  {
    return positionAfterlesser;
  }
  uint32_t lesser = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field greater */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - positionAfterlesser);
  uint64_t positionAftergreater_refinement;
  if (hasBytes)
  {
    positionAftergreater_refinement = positionAfterlesser + (uint64_t)4U;
  }
  else
  {
    positionAftergreater_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterlesser);
  }
  uint64_t positionAfterOrderedPair0;
  if (EverParseIsError(positionAftergreater_refinement))
  {
    positionAfterOrderedPair0 = positionAftergreater_refinement;
  }
  else
  {
    /* reading field_value */
    uint32_t greater_refinement = Load32Le(Input + (uint32_t)positionAfterlesser);
    /* start: checking constraint */
    BOOLEAN greater_refinementConstraintIsOk = lesser <= greater_refinement;
    /* end: checking constraint */
    positionAfterOrderedPair0 =
      EverParseCheckConstraintOk(greater_refinementConstraintIsOk,
        positionAftergreater_refinement);
  }
  if (EverParseIsSuccess(positionAfterOrderedPair0))
  {
    return positionAfterOrderedPair0;
  }
  ErrorHandlerFn("_orderedPair",
    "greater.refinement",
    EverParseErrorReasonOfResult(positionAfterOrderedPair0),
    EverParseGetValidatorErrorKind(positionAfterOrderedPair0),
    Ctxt,
    Input,
    positionAfterlesser);
  return positionAfterOrderedPair0;
}

