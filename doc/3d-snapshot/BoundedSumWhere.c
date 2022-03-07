

#include "BoundedSumWhere.h"



uint64_t
BoundedSumWhereValidateBoundedSum(
  uint32_t Bound,
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  uint64_t positionAfternone = StartPosition;
  uint64_t positionAfterBoundedSum;
  if (EverParseIsError(positionAfternone))
  {
    positionAfterBoundedSum = positionAfternone;
  }
  else
  {
    BOOLEAN noneConstraintIsOk = Bound <= (uint32_t)(uint16_t)1729U;
    uint64_t
    positionAfternone1 = EverParseCheckConstraintOk(noneConstraintIsOk, positionAfternone);
    if (EverParseIsError(positionAfternone1))
    {
      positionAfterBoundedSum = positionAfternone1;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      BOOLEAN hasBytes0 = (uint64_t)4U <= (InputLength - positionAfternone1);
      uint64_t positionAfterBoundedSum0;
      if (hasBytes0)
      {
        positionAfterBoundedSum0 = positionAfternone1 + (uint64_t)4U;
      }
      else
      {
        positionAfterBoundedSum0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfternone1);
      }
      uint64_t positionAfterleft;
      if (EverParseIsSuccess(positionAfterBoundedSum0))
      {
        positionAfterleft = positionAfterBoundedSum0;
      }
      else
      {
        Err("_boundedSum",
          "left",
          EverParseErrorReasonOfResult(positionAfterBoundedSum0),
          Ctxt,
          Input,
          positionAfternone1);
        positionAfterleft = positionAfterBoundedSum0;
      }
      if (EverParseIsError(positionAfterleft))
      {
        positionAfterBoundedSum = positionAfterleft;
      }
      else
      {
        uint32_t left = Load32Le(Input + (uint32_t)positionAfternone1);
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
          BOOLEAN
          right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
          /* end: checking constraint */
          positionAfterBoundedSum0 =
            EverParseCheckConstraintOk(right_refinementConstraintIsOk,
              positionAfterright_refinement);
        }
        if (EverParseIsSuccess(positionAfterBoundedSum0))
        {
          positionAfterBoundedSum = positionAfterBoundedSum0;
        }
        else
        {
          Err("_boundedSum",
            "right.refinement",
            EverParseErrorReasonOfResult(positionAfterBoundedSum0),
            Ctxt,
            Input,
            positionAfterleft);
          positionAfterBoundedSum = positionAfterBoundedSum0;
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    return positionAfterBoundedSum;
  }
  Err("_boundedSum",
    "none",
    EverParseErrorReasonOfResult(positionAfterBoundedSum),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterBoundedSum;
}

