

#include "BoundedSumWhere.h"

#include "EverParse.h"

uint64_t
BoundedSumWhereValidateBoundedSum(
  uint32_t Bound,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  uint64_t positionAfterPrecondition = StartPosition;
  uint64_t positionAfterPrecondition0;
  BOOLEAN preconditionConstraintIsOk;
  uint64_t positionAfterCheckedPrecondition;
  BOOLEAN hasBytes0;
  uint64_t positionAfterleft0;
  uint64_t positionAfterleft;
  uint32_t left;
  BOOLEAN hasBytes;
  uint64_t positionAfterright_refinement;
  uint64_t positionAfterright_refinement0;
  uint32_t right_refinement;
  BOOLEAN right_refinementConstraintIsOk;
  if (EverParseIsError(positionAfterPrecondition))
  {
    positionAfterPrecondition0 = positionAfterPrecondition;
  }
  else
  {
    preconditionConstraintIsOk = Bound <= 1729U;
    positionAfterCheckedPrecondition =
      EverParseCheckConstraintOk(preconditionConstraintIsOk,
        positionAfterPrecondition);
    if (EverParseIsError(positionAfterCheckedPrecondition))
    {
      positionAfterPrecondition0 = positionAfterCheckedPrecondition;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      hasBytes0 = (InputLength - positionAfterCheckedPrecondition) >= 4ULL;
      if (hasBytes0)
      {
        positionAfterleft0 = positionAfterCheckedPrecondition + 4ULL;
      }
      else
      {
        positionAfterleft0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedPrecondition);
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
          positionAfterCheckedPrecondition);
        positionAfterleft = positionAfterleft0;
      }
      if (EverParseIsError(positionAfterleft))
      {
        positionAfterPrecondition0 = positionAfterleft;
      }
      else
      {
        left = Load32Le(Input + (uint32_t)positionAfterCheckedPrecondition);
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
          right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
          /* end: checking constraint */
          positionAfterright_refinement0 =
            EverParseCheckConstraintOk(right_refinementConstraintIsOk,
              positionAfterright_refinement);
        }
        if (EverParseIsSuccess(positionAfterright_refinement0))
        {
          positionAfterPrecondition0 = positionAfterright_refinement0;
        }
        else
        {
          ErrorHandlerFn("_boundedSum",
            "right.refinement",
            EverParseErrorReasonOfResult(positionAfterright_refinement0),
            EverParseGetValidatorErrorKind(positionAfterright_refinement0),
            Ctxt,
            Input,
            positionAfterleft);
          positionAfterPrecondition0 = positionAfterright_refinement0;
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfterPrecondition0))
  {
    return positionAfterPrecondition0;
  }
  ErrorHandlerFn("_boundedSum",
    "__precondition",
    EverParseErrorReasonOfResult(positionAfterPrecondition0),
    EverParseGetValidatorErrorKind(positionAfterPrecondition0),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPrecondition0;
}

