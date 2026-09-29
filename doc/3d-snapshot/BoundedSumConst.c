

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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterleft0;
  uint64_t positionAfterleft;
  uint32_t left;
  BOOLEAN hasBytes;
  uint64_t positionAfterright_refinement;
  uint64_t positionAfterright_refinement0;
  uint32_t right_refinement;
  BOOLEAN right_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAfterleft0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterleft0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterleft0))
  {
    positionAfterleft = positionAfterleft0;
  }
  else
  {
    ErrorHandlerFn("_boundedSum",
      "left",
      EverParseErrorReasonOfResult(positionAfterleft0),
      EverParseGetValidatorErrorKind(positionAfterleft0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterleft = positionAfterleft0;
  }
  if (EverParseIsError(positionAfterleft))
  {
    return positionAfterleft;
  }
  left = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field right */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterleft) >= 4ULL;
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
    positionAfterright_refinement0 = positionAfterright_refinement;
  }
  else
  {
    /* reading field_value */
    right_refinement = Load32Le(Input + (uint32_t)positionAfterleft);
    /* start: checking constraint */
    right_refinementConstraintIsOk = left <= 42U && right_refinement <= ((uint32_t)42U - left);
    /* end: checking constraint */
    positionAfterright_refinement0 =
      EverParseCheckConstraintOk(right_refinementConstraintIsOk,
        positionAfterright_refinement);
  }
  if (EverParseIsSuccess(positionAfterright_refinement0))
  {
    return positionAfterright_refinement0;
  }
  ErrorHandlerFn("_boundedSum",
    "right.refinement",
    EverParseErrorReasonOfResult(positionAfterright_refinement0),
    EverParseGetValidatorErrorKind(positionAfterright_refinement0),
    Ctxt,
    Input,
    positionAfterleft);
  return positionAfterright_refinement0;
}

