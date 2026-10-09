

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
  uint64_t positionAfterPreconditionOrError;
  BOOLEAN preconditionConstraintIsOk;
  uint64_t positionAfterCheckedPrecondition;
  BOOLEAN hasBytesForLeft;
  uint64_t positionAfterLeftOrError;
  uint64_t positionAfterLeft;
  uint32_t left;
  BOOLEAN hasBytesForRight_refinement;
  uint64_t positionAfterRight_refinement;
  uint64_t positionAfterRight_refinementOrError;
  uint32_t right_refinement;
  BOOLEAN right_refinementConstraintIsOk;
  if (EverParseIsError(positionAfterPrecondition))
  {
    positionAfterPreconditionOrError = positionAfterPrecondition;
  }
  else
  {
    preconditionConstraintIsOk = Bound <= 1729U;
    positionAfterCheckedPrecondition =
      EverParseCheckConstraintOk(preconditionConstraintIsOk,
        positionAfterPrecondition);
    if (EverParseIsError(positionAfterCheckedPrecondition))
    {
      positionAfterPreconditionOrError = positionAfterCheckedPrecondition;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      hasBytesForLeft = (InputLength - positionAfterCheckedPrecondition) >= 4ULL;
      if (hasBytesForLeft)
      {
        positionAfterLeftOrError = positionAfterCheckedPrecondition + 4ULL;
      }
      else
      {
        positionAfterLeftOrError =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedPrecondition);
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
          positionAfterCheckedPrecondition);
        positionAfterLeft = positionAfterLeftOrError;
      }
      if (EverParseIsError(positionAfterLeft))
      {
        positionAfterPreconditionOrError = positionAfterLeft;
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
          positionAfterRight_refinementOrError = positionAfterRight_refinement;
        }
        else
        {
          /* reading field_value */
          right_refinement = Load32Le(Input + (uint32_t)positionAfterLeft);
          /* start: checking constraint */
          right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
          /* end: checking constraint */
          positionAfterRight_refinementOrError =
            EverParseCheckConstraintOk(right_refinementConstraintIsOk,
              positionAfterRight_refinement);
        }
        if (EverParseIsSuccess(positionAfterRight_refinementOrError))
        {
          positionAfterPreconditionOrError = positionAfterRight_refinementOrError;
        }
        else
        {
          ErrorHandlerFn("_boundedSum",
            "right.refinement",
            EverParseErrorReasonOfResult(positionAfterRight_refinementOrError),
            EverParseGetValidatorErrorKind(positionAfterRight_refinementOrError),
            Ctxt,
            Input,
            positionAfterLeft);
          positionAfterPreconditionOrError = positionAfterRight_refinementOrError;
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfterPreconditionOrError))
  {
    return positionAfterPreconditionOrError;
  }
  ErrorHandlerFn("_boundedSum",
    "__precondition",
    EverParseErrorReasonOfResult(positionAfterPreconditionOrError),
    EverParseGetValidatorErrorKind(positionAfterPreconditionOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPreconditionOrError;
}

