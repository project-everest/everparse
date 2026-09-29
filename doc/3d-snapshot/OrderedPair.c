

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
  uint64_t positionAfterLesser0;
  uint64_t positionAfterLesser;
  uint32_t lesser;
  BOOLEAN hasBytes;
  uint64_t positionAfterGreater_refinement;
  uint64_t positionAfterGreater_refinement0;
  uint32_t greater_refinement;
  BOOLEAN greater_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAfterLesser0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterLesser0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterLesser0))
  {
    positionAfterLesser = positionAfterLesser0;
  }
  else
  {
    ErrorHandlerFn("_orderedPair",
      "lesser",
      EverParseErrorReasonOfResult(positionAfterLesser0),
      EverParseGetValidatorErrorKind(positionAfterLesser0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterLesser = positionAfterLesser0;
  }
  if (EverParseIsError(positionAfterLesser))
  {
    return positionAfterLesser;
  }
  lesser = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field greater */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterLesser) >= 4ULL;
  if (hasBytes)
  {
    positionAfterGreater_refinement = positionAfterLesser + 4ULL;
  }
  else
  {
    positionAfterGreater_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterLesser);
  }
  if (EverParseIsError(positionAfterGreater_refinement))
  {
    positionAfterGreater_refinement0 = positionAfterGreater_refinement;
  }
  else
  {
    /* reading field_value */
    greater_refinement = Load32Le(Input + (uint32_t)positionAfterLesser);
    /* start: checking constraint */
    greater_refinementConstraintIsOk = lesser <= greater_refinement;
    /* end: checking constraint */
    positionAfterGreater_refinement0 =
      EverParseCheckConstraintOk(greater_refinementConstraintIsOk,
        positionAfterGreater_refinement);
  }
  if (EverParseIsSuccess(positionAfterGreater_refinement0))
  {
    return positionAfterGreater_refinement0;
  }
  ErrorHandlerFn("_orderedPair",
    "greater.refinement",
    EverParseErrorReasonOfResult(positionAfterGreater_refinement0),
    EverParseGetValidatorErrorKind(positionAfterGreater_refinement0),
    Ctxt,
    Input,
    positionAfterLesser);
  return positionAfterGreater_refinement0;
}

