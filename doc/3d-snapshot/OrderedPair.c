

#include "OrderedPair.h"

#include "EverParse.h"

uint64_t
OrderedPairValidateOrderedPair(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterlesser0;
  uint64_t positionAfterlesser;
  uint32_t lesser;
  BOOLEAN hasBytes;
  uint64_t positionAftergreater_refinement;
  uint64_t positionAftergreater_refinement0;
  uint32_t greater_refinement;
  BOOLEAN greater_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAfterlesser0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterlesser0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterlesser0))
  {
    positionAfterlesser = positionAfterlesser0;
  }
  else
  {
    ErrorHandlerFn("_orderedPair",
      "lesser",
      EverParseErrorReasonOfResult(positionAfterlesser0),
      EverParseGetValidatorErrorKind(positionAfterlesser0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterlesser = positionAfterlesser0;
  }
  if (EverParseIsError(positionAfterlesser))
  {
    return positionAfterlesser;
  }
  lesser = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field greater */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterlesser) >= 4ULL;
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
    positionAftergreater_refinement0 = positionAftergreater_refinement;
  }
  else
  {
    /* reading field_value */
    greater_refinement = Load32Le(Input + (uint32_t)positionAfterlesser);
    /* start: checking constraint */
    greater_refinementConstraintIsOk = lesser <= greater_refinement;
    /* end: checking constraint */
    positionAftergreater_refinement0 =
      EverParseCheckConstraintOk(greater_refinementConstraintIsOk,
        positionAftergreater_refinement);
  }
  if (EverParseIsSuccess(positionAftergreater_refinement0))
  {
    return positionAftergreater_refinement0;
  }
  ErrorHandlerFn("_orderedPair",
    "greater.refinement",
    EverParseErrorReasonOfResult(positionAftergreater_refinement0),
    EverParseGetValidatorErrorKind(positionAftergreater_refinement0),
    Ctxt,
    Input,
    positionAfterlesser);
  return positionAftergreater_refinement0;
}

