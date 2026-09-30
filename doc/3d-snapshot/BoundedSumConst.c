

#include "BoundedSumConst.h"

#include "EverParse.h"

uint64_t
BoundedSumConstValidateBoundedSum(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytesForLeft = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterLeftOrError;
  uint64_t positionAfterLeft;
  uint32_t left;
  BOOLEAN hasBytesForRight_refinement;
  uint64_t positionAfterRight_refinement;
  uint64_t positionAfterRight_refinementOrError;
  uint32_t right_refinement;
  BOOLEAN right_refinementConstraintIsOk;
  if (hasBytesForLeft)
  {
    positionAfterLeftOrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterLeftOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterLeftOrError))
  {
    positionAfterLeft = positionAfterLeftOrError;
  }
  else
  {
    ErrorHandlerFn("_boundedSum",
      "left",
      EverParseErrorReasonOfResult(positionAfterLeftOrError),
      EverParseGetValidatorErrorKind(positionAfterLeftOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterLeft = positionAfterLeftOrError;
  }
  if (EverParseIsError(positionAfterLeft))
  {
    return positionAfterLeft;
  }
  left = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field right */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytesForRight_refinement = (InputLength - positionAfterLeft) >= 4ULL;
  if (hasBytesForRight_refinement)
  {
    positionAfterRight_refinement = positionAfterLeft + 4ULL;
  }
  else
  {
    positionAfterRight_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterLeft);
  }
  if (EverParseIsError(positionAfterRight_refinement))
  {
    positionAfterRight_refinementOrError = positionAfterRight_refinement;
  }
  else
  {
    /* reading field_value */
    right_refinement = Load32Le(Input + (uint32_t)positionAfterLeft);
    /* start: checking constraint */
    right_refinementConstraintIsOk = left <= 42U && right_refinement <= ((uint32_t)42U - left);
    /* end: checking constraint */
    positionAfterRight_refinementOrError =
      EverParseCheckConstraintOk(right_refinementConstraintIsOk,
        positionAfterRight_refinement);
  }
  if (EverParseIsSuccess(positionAfterRight_refinementOrError))
  {
    return positionAfterRight_refinementOrError;
  }
  ErrorHandlerFn("_boundedSum",
    "right.refinement",
    EverParseErrorReasonOfResult(positionAfterRight_refinementOrError),
    EverParseGetValidatorErrorKind(positionAfterRight_refinementOrError),
    Ctxt,
    Input,
    positionAfterLeft);
  return positionAfterRight_refinementOrError;
}

