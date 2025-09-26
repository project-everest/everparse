

#include "EnumConstraint.h"

uint64_t
EnumConstraintValidateEnumConstraint(
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
  uint64_t positionAftercol;
  if (hasBytes0)
  {
    positionAftercol = StartPosition + 4ULL;
  }
  else
  {
    positionAftercol =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterEnumConstraint;
  if (EverParseIsError(positionAftercol))
  {
    positionAfterEnumConstraint = positionAftercol;
  }
  else
  {
    uint32_t col = Load32Le(Input + (uint32_t)StartPosition);
    BOOLEAN
    colConstraintIsOk =
      col == ENUMCONSTRAINT_RED || col == ENUMCONSTRAINT_GREEN || col == ENUMCONSTRAINT_BLUE;
    uint64_t positionAftercol1 = EverParseCheckConstraintOk(colConstraintIsOk, positionAftercol);
    if (EverParseIsError(positionAftercol1))
    {
      positionAfterEnumConstraint = positionAftercol1;
    }
    else
    {
      /* Validating field x */
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      BOOLEAN hasBytes = 4ULL <= (InputLength - positionAftercol1);
      uint64_t positionAfterx_refinement;
      if (hasBytes)
      {
        positionAfterx_refinement = positionAftercol1 + 4ULL;
      }
      else
      {
        positionAfterx_refinement =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAftercol1);
      }
      uint64_t positionAfterEnumConstraint0;
      if (EverParseIsError(positionAfterx_refinement))
      {
        positionAfterEnumConstraint0 = positionAfterx_refinement;
      }
      else
      {
        /* reading field_value */
        uint32_t x_refinement = Load32Le(Input + (uint32_t)positionAftercol1);
        /* start: checking constraint */
        BOOLEAN
        x_refinementConstraintIsOk = x_refinement == (uint32_t)0U || col == ENUMCONSTRAINT_GREEN;
        /* end: checking constraint */
        positionAfterEnumConstraint0 =
          EverParseCheckConstraintOk(x_refinementConstraintIsOk,
            positionAfterx_refinement);
      }
      if (EverParseIsSuccess(positionAfterEnumConstraint0))
      {
        positionAfterEnumConstraint = positionAfterEnumConstraint0;
      }
      else
      {
        ErrorHandlerFn("_enum_constraint",
          "x.refinement",
          EverParseErrorReasonOfResult(positionAfterEnumConstraint0),
          EverParseGetValidatorErrorKind(positionAfterEnumConstraint0),
          Ctxt,
          Input,
          positionAftercol1);
        positionAfterEnumConstraint = positionAfterEnumConstraint0;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterEnumConstraint))
  {
    return positionAfterEnumConstraint;
  }
  ErrorHandlerFn("_enum_constraint",
    "col",
    EverParseErrorReasonOfResult(positionAfterEnumConstraint),
    EverParseGetValidatorErrorKind(positionAfterEnumConstraint),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterEnumConstraint;
}

