

#include "BoundedSum.h"



uint64_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t positionAfterBoundedSum;
  if (hasBytes0)
  {
    positionAfterBoundedSum = StartPosition + (uint64_t)4U;
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
    Err("_boundedSum",
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
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - positionAfterleft);
  uint64_t positionAfterright_refinement;
  if (hasBytes)
  {
    positionAfterright_refinement = positionAfterleft + (uint64_t)4U;
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
    BOOLEAN right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
    /* end: checking constraint */
    positionAfterBoundedSum0 =
      EverParseCheckConstraintOk(right_refinementConstraintIsOk,
        positionAfterright_refinement);
  }
  if (EverParseIsSuccess(positionAfterBoundedSum0))
  {
    return positionAfterBoundedSum0;
  }
  Err("_boundedSum",
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
  (*Err)(
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
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAftermySum;
  if (hasBytes)
  {
    positionAftermySum = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAftermySum =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterbound;
  if (EverParseIsSuccess(positionAftermySum))
  {
    positionAfterbound = positionAftermySum;
  }
  else
  {
    Err("mySum",
      "bound",
      EverParseErrorReasonOfResult(positionAftermySum),
      EverParseGetValidatorErrorKind(positionAftermySum),
      Ctxt,
      Input,
      StartPosition);
    positionAfterbound = positionAftermySum;
  }
  if (EverParseIsError(positionAfterbound))
  {
    return positionAfterbound;
  }
  uint32_t bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field sum */
  uint64_t
  positionAftermySum0 =
    BoundedSumValidateBoundedSum(bound,
      Ctxt,
      Err,
      Input,
      InputLength,
      positionAfterbound);
  if (EverParseIsSuccess(positionAftermySum0))
  {
    return positionAftermySum0;
  }
  Err("mySum",
    "sum",
    EverParseErrorReasonOfResult(positionAftermySum0),
    EverParseGetValidatorErrorKind(positionAftermySum0),
    Ctxt,
    Input,
    positionAfterbound);
  return positionAftermySum0;
}

