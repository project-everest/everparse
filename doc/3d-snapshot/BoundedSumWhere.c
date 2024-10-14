

#include "BoundedSumWhere.h"

uint64_t
BoundedSumWhereValidateBoundedSum(
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
  uint64_t positionAfterPrecondition = StartPosition;
  uint64_t positionAfterBoundedSum;
  if (EverParseIsError(positionAfterPrecondition))
  {
    positionAfterBoundedSum = positionAfterPrecondition;
  }
  else
  {
    BOOLEAN preconditionConstraintIsOk = Bound <= (uint32_t)1729U;
    uint64_t
    positionAfterPrecondition1 =
      EverParseCheckConstraintOk(preconditionConstraintIsOk,
        positionAfterPrecondition);
    if (EverParseIsError(positionAfterPrecondition1))
    {
      positionAfterBoundedSum = positionAfterPrecondition1;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      BOOLEAN hasBytes0 = 4ULL <= (InputLength - positionAfterPrecondition1);
      uint64_t positionAfterBoundedSum0;
      if (hasBytes0)
      {
        positionAfterBoundedSum0 = positionAfterPrecondition1 + 4ULL;
      }
      else
      {
        positionAfterBoundedSum0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterPrecondition1);
      }
      uint64_t positionAfterleft;
      if (EverParseIsSuccess(positionAfterBoundedSum0))
      {
        positionAfterleft = positionAfterBoundedSum0;
      }
      else
      {
        ErrorHandlerFn("_boundedSum",
          "left",
          EverParseErrorReasonOfResult(positionAfterBoundedSum0),
          EverParseGetValidatorErrorKind(positionAfterBoundedSum0),
          Ctxt,
          Input,
          positionAfterPrecondition1);
        positionAfterleft = positionAfterBoundedSum0;
      }
      if (EverParseIsError(positionAfterleft))
      {
        positionAfterBoundedSum = positionAfterleft;
      }
      else
      {
        uint32_t left = Load32Le(Input + (uint32_t)positionAfterPrecondition1);
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
        uint64_t positionAfterBoundedSum1;
        if (EverParseIsError(positionAfterright_refinement))
        {
          positionAfterBoundedSum1 = positionAfterright_refinement;
        }
        else
        {
          /* reading field_value */
          uint32_t right_refinement = Load32Le(Input + (uint32_t)positionAfterleft);
          /* start: checking constraint */
          BOOLEAN
          right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
          /* end: checking constraint */
          positionAfterBoundedSum1 =
            EverParseCheckConstraintOk(right_refinementConstraintIsOk,
              positionAfterright_refinement);
        }
        if (EverParseIsSuccess(positionAfterBoundedSum1))
        {
          positionAfterBoundedSum = positionAfterBoundedSum1;
        }
        else
        {
          ErrorHandlerFn("_boundedSum",
            "right.refinement",
            EverParseErrorReasonOfResult(positionAfterBoundedSum1),
            EverParseGetValidatorErrorKind(positionAfterBoundedSum1),
            Ctxt,
            Input,
            positionAfterleft);
          positionAfterBoundedSum = positionAfterBoundedSum1;
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    return positionAfterBoundedSum;
  }
  ErrorHandlerFn("_boundedSum",
    "__precondition",
    EverParseErrorReasonOfResult(positionAfterBoundedSum),
    EverParseGetValidatorErrorKind(positionAfterBoundedSum),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterBoundedSum;
}

