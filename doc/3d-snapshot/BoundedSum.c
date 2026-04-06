

#include "BoundedSum.h"

uint64_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
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
  uint64_t positionAfterBoundedSum;
  uint64_t positionAfterleft;
  uint32_t left;
  BOOLEAN hasBytes;
  uint64_t positionAfterright_refinement;
  uint64_t positionAfterBoundedSum0;
  uint32_t right_refinement;
  BOOLEAN right_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAfterBoundedSum = StartPosition + 4ULL;
  }
  else
  {
    positionAfterBoundedSum =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    positionAfterleft = positionAfterBoundedSum;
  }
  else
  {
    ErrorHandlerFn("_boundedSum",
      "left",
      EverParseErrorReasonOfResult(positionAfterBoundedSum),
      EverParseGetValidatorErrorKind(positionAfterBoundedSum),
      Ctxt,
      Input,
      StartPosition);
    positionAfterleft = positionAfterBoundedSum;
  }
  if (EverParseIsError(positionAfterleft))
  {
    return positionAfterleft;
  }
  left = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field right */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = 4ULL <= (InputLength - positionAfterleft);
  if (hasBytes)
  {
    positionAfterright_refinement = positionAfterleft + 4ULL;
  }
  else
  {
    positionAfterright_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterleft);
  }
  if (EverParseIsError(positionAfterright_refinement))
  {
    positionAfterBoundedSum0 = positionAfterright_refinement;
  }
  else
  {
    /* reading field_value */
    right_refinement = Load32Le(Input + (uint32_t)positionAfterleft);
    /* start: checking constraint */
    right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
    /* end: checking constraint */
    positionAfterBoundedSum0 =
      EverParseCheckConstraintOk(right_refinementConstraintIsOk,
        positionAfterright_refinement);
  }
  if (EverParseIsSuccess(positionAfterBoundedSum0))
  {
    return positionAfterBoundedSum0;
  }
  ErrorHandlerFn("_boundedSum",
    "right.refinement",
    EverParseErrorReasonOfResult(positionAfterBoundedSum0),
    EverParseGetValidatorErrorKind(positionAfterBoundedSum0),
    Ctxt,
    Input,
    positionAfterleft);
  return positionAfterBoundedSum0;
}

uint64_t
BoundedSumValidateMySum(
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
  BOOLEAN hasBytes = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAftermySum0;
  uint64_t positionAfterbound;
  uint32_t bound;
  uint64_t positionAftermySum;
  if (hasBytes)
  {
    positionAftermySum0 = StartPosition + 4ULL;
  }
  else
  {
    positionAftermySum0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAftermySum0))
  {
    positionAfterbound = positionAftermySum0;
  }
  else
  {
    ErrorHandlerFn("mySum",
      "bound",
      EverParseErrorReasonOfResult(positionAftermySum0),
      EverParseGetValidatorErrorKind(positionAftermySum0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterbound = positionAftermySum0;
  }
  if (EverParseIsError(positionAfterbound))
  {
    return positionAfterbound;
  }
  bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field sum */
  positionAftermySum =
    BoundedSumValidateBoundedSum(bound,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAfterbound);
  if (EverParseIsSuccess(positionAftermySum))
  {
    return positionAftermySum;
  }
  ErrorHandlerFn("mySum",
    "sum",
    EverParseErrorReasonOfResult(positionAftermySum),
    EverParseGetValidatorErrorKind(positionAftermySum),
    Ctxt,
    Input,
    positionAfterbound);
  return positionAftermySum;
}

