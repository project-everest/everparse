

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
  BOOLEAN hasBytesForLesser = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterLesserOrError;
  uint64_t positionAfterLesser;
  uint32_t lesser;
  BOOLEAN hasBytesForGreater_refinement;
  uint64_t positionAfterGreater_refinement;
  uint64_t positionAfterGreater_refinementOrError;
  uint32_t greater_refinement;
  BOOLEAN greater_refinementConstraintIsOk;
  if (hasBytesForLesser)
  {
    positionAfterLesserOrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterLesserOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterLesserOrError))
  {
    positionAfterLesser = positionAfterLesserOrError;
  }
  else
  {
    ErrorHandlerFn("_orderedPair",
      "lesser",
      EverParseErrorReasonOfResult(positionAfterLesserOrError),
      EverParseGetValidatorErrorKind(positionAfterLesserOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterLesser = positionAfterLesserOrError;
  }
  if (EverParseIsError(positionAfterLesser))
  {
    return positionAfterLesser;
  }
  lesser = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field greater */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytesForGreater_refinement = (InputLength - positionAfterLesser) >= 4ULL;
  if (hasBytesForGreater_refinement)
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
    positionAfterGreater_refinementOrError = positionAfterGreater_refinement;
  }
  else
  {
    /* reading field_value */
    greater_refinement = Load32Le(Input + (uint32_t)positionAfterLesser);
    /* start: checking constraint */
    greater_refinementConstraintIsOk = lesser <= greater_refinement;
    /* end: checking constraint */
    positionAfterGreater_refinementOrError =
      EverParseCheckConstraintOk(greater_refinementConstraintIsOk,
        positionAfterGreater_refinement);
  }
  if (EverParseIsSuccess(positionAfterGreater_refinementOrError))
  {
    return positionAfterGreater_refinementOrError;
  }
  ErrorHandlerFn("_orderedPair",
    "greater.refinement",
    EverParseErrorReasonOfResult(positionAfterGreater_refinementOrError),
    EverParseGetValidatorErrorKind(positionAfterGreater_refinementOrError),
    Ctxt,
    Input,
    positionAfterLesser);
  return positionAfterGreater_refinementOrError;
}

