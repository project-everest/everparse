

#include "BoundedSumConst.h"

uint64_t
BoundedSumConstValidateBoundedSum(
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
  uint64_t positionAfterleft;
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
  uint32_t left = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field right */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = 4ULL <= (InputLength - positionAfterleft);
  uint64_t positionAfterright_refinement;
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
  uint64_t positionAfterBoundedSum0;
  if (EverParseIsError(positionAfterright_refinement))
  {
    positionAfterBoundedSum0 = positionAfterright_refinement;
  }
  else
  {
    /* reading field_value */
    uint32_t right_refinement = Load32Le(Input + (uint32_t)positionAfterleft);
    /* start: checking constraint */
    BOOLEAN
    right_refinementConstraintIsOk =
      left <= (uint32_t)42U && right_refinement <= ((uint32_t)42U - left);
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

