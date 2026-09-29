

#include "BoundedSum.h"

#include "EverParse.h"

uint64_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterLeft0;
  uint64_t positionAfterLeft;
  uint32_t left;
  BOOLEAN hasBytes;
  uint64_t positionAfterRight_refinement;
  uint64_t positionAfterRight_refinement0;
  uint32_t right_refinement;
  BOOLEAN right_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAfterLeft0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterLeft0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterLeft0))
  {
    positionAfterLeft = positionAfterLeft0;
  }
  else
  {
    ErrorHandlerFn("_boundedSum",
      "left",
      EverParseErrorReasonOfResult(positionAfterLeft0),
      EverParseGetValidatorErrorKind(positionAfterLeft0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterLeft = positionAfterLeft0;
  }
  if (EverParseIsError(positionAfterLeft))
  {
    return positionAfterLeft;
  }
  left = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field right */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterLeft) >= 4ULL;
  if (hasBytes)
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
    positionAfterRight_refinement0 = positionAfterRight_refinement;
  }
  else
  {
    /* reading field_value */
    right_refinement = Load32Le(Input + (uint32_t)positionAfterLeft);
    /* start: checking constraint */
    right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
    /* end: checking constraint */
    positionAfterRight_refinement0 =
      EverParseCheckConstraintOk(right_refinementConstraintIsOk,
        positionAfterRight_refinement);
  }
  if (EverParseIsSuccess(positionAfterRight_refinement0))
  {
    return positionAfterRight_refinement0;
  }
  ErrorHandlerFn("_boundedSum",
    "right.refinement",
    EverParseErrorReasonOfResult(positionAfterRight_refinement0),
    EverParseGetValidatorErrorKind(positionAfterRight_refinement0),
    Ctxt,
    Input,
    positionAfterLeft);
  return positionAfterRight_refinement0;
}

uint64_t
BoundedSumValidateMySum(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterBound0;
  uint64_t positionAfterBound;
  uint32_t bound;
  uint64_t positionAfterSum;
  if (hasBytes)
  {
    positionAfterBound0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterBound0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBound0))
  {
    positionAfterBound = positionAfterBound0;
  }
  else
  {
    ErrorHandlerFn("mySum",
      "bound",
      EverParseErrorReasonOfResult(positionAfterBound0),
      EverParseGetValidatorErrorKind(positionAfterBound0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBound = positionAfterBound0;
  }
  if (EverParseIsError(positionAfterBound))
  {
    return positionAfterBound;
  }
  bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field sum */
  positionAfterSum =
    BoundedSumValidateBoundedSum(bound,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAfterBound);
  if (EverParseIsSuccess(positionAfterSum))
  {
    return positionAfterSum;
  }
  ErrorHandlerFn("mySum",
    "sum",
    EverParseErrorReasonOfResult(positionAfterSum),
    EverParseGetValidatorErrorKind(positionAfterSum),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterSum;
}

