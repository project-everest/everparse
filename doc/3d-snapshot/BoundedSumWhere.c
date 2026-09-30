

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
  BOOLEAN hasBytesForLeft;
  uint64_t positionAfterLeft0;
  uint64_t positionAfterLeft;
  uint32_t left;
  BOOLEAN hasBytesForRight_refinement;
  uint64_t positionAfterRight_refinement;
  uint64_t positionAfterRight_refinement0;
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
      hasBytesForLeft = (InputLength - positionAfterCheckedPrecondition) >= 4ULL;
      if (hasBytesForLeft)
      {
        positionAfterLeft0 = positionAfterCheckedPrecondition + 4ULL;
      }
      else
      {
        positionAfterLeft0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedPrecondition);
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
          positionAfterCheckedPrecondition);
        positionAfterLeft = positionAfterLeft0;
      }
      if (EverParseIsError(positionAfterLeft))
      {
        positionAfterPrecondition0 = positionAfterLeft;
      }
      else
      {
        left = Load32Le(Input + (uint32_t)positionAfterCheckedPrecondition);
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
          positionAfterPrecondition0 = positionAfterRight_refinement0;
        }
        else
        {
          ErrorHandlerFn("_boundedSum",
            "right.refinement",
            EverParseErrorReasonOfResult(positionAfterRight_refinement0),
            EverParseGetValidatorErrorKind(positionAfterRight_refinement0),
            Ctxt,
            Input,
            positionAfterLeft);
          positionAfterPrecondition0 = positionAfterRight_refinement0;
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

