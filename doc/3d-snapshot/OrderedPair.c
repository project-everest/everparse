

#include "OrderedPair.h"

uint64_t
OrderedPairValidateOrderedPair(
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
  uint64_t positionAfterOrderedPair;
  uint64_t positionAfterlesser;
  uint32_t lesser;
  BOOLEAN hasBytes;
  uint64_t positionAftergreater_refinement;
  uint64_t positionAfterOrderedPair0;
  uint32_t greater_refinement;
  BOOLEAN greater_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAfterOrderedPair = StartPosition + 4ULL;
  }
  else
  {
    positionAfterOrderedPair =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
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
  lesser = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field greater */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = 4ULL <= (InputLength - positionAfterlesser);
  if (hasBytes)
  {
    positionAftergreater_refinement = positionAfterlesser + 4ULL;
  }
  else
  {
    positionAftergreater_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterlesser);
  }
  if (EverParseIsError(positionAftergreater_refinement))
  {
    positionAfterOrderedPair0 = positionAftergreater_refinement;
  }
  else
  {
    /* reading field_value */
    greater_refinement = Load32Le(Input + (uint32_t)positionAfterlesser);
    /* start: checking constraint */
    greater_refinementConstraintIsOk = lesser <= greater_refinement;
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

