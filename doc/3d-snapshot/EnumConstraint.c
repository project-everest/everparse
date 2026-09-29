

#include "EnumConstraint.h"

#include "EverParse.h"

uint64_t
EnumConstraintValidateEnumConstraint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAftercol0;
  uint64_t positionAftercol;
  uint32_t col;
  BOOLEAN colConstraintIsOk;
  uint64_t positionAfterCheckedcol;
  BOOLEAN hasBytes;
  uint64_t positionAfterx_refinement;
  uint64_t positionAfterx_refinement0;
  uint32_t x_refinement;
  BOOLEAN x_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAftercol0 = StartPosition + 4ULL;
  }
  else
  {
    positionAftercol0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAftercol0))
  {
    positionAftercol = positionAftercol0;
  }
  else
  {
    col = Load32Le(Input + (uint32_t)StartPosition);
    colConstraintIsOk =
      col == ENUMCONSTRAINT_RED || col == ENUMCONSTRAINT_GREEN || col == ENUMCONSTRAINT_BLUE;
    positionAfterCheckedcol = EverParseCheckConstraintOk(colConstraintIsOk, positionAftercol0);
    if (EverParseIsError(positionAfterCheckedcol))
    {
      positionAftercol = positionAfterCheckedcol;
    }
    else
    {
      /* Validating field x */
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      hasBytes = (InputLength - positionAfterCheckedcol) >= 4ULL;
      if (hasBytes)
      {
        positionAfterx_refinement = positionAfterCheckedcol + 4ULL;
      }
      else
      {
        positionAfterx_refinement =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedcol);
      }
      if (EverParseIsError(positionAfterx_refinement))
      {
        positionAfterx_refinement0 = positionAfterx_refinement;
      }
      else
      {
        /* reading field_value */
        x_refinement = Load32Le(Input + (uint32_t)positionAfterCheckedcol);
        /* start: checking constraint */
        x_refinementConstraintIsOk = x_refinement == 0U || col == ENUMCONSTRAINT_GREEN;
        /* end: checking constraint */
        positionAfterx_refinement0 =
          EverParseCheckConstraintOk(x_refinementConstraintIsOk,
            positionAfterx_refinement);
      }
      if (EverParseIsSuccess(positionAfterx_refinement0))
      {
        positionAftercol = positionAfterx_refinement0;
      }
      else
      {
        ErrorHandlerFn("_enum_constraint",
          "x.refinement",
          EverParseErrorReasonOfResult(positionAfterx_refinement0),
          EverParseGetValidatorErrorKind(positionAfterx_refinement0),
          Ctxt,
          Input,
          positionAfterCheckedcol);
        positionAftercol = positionAfterx_refinement0;
      }
    }
  }
  if (EverParseIsSuccess(positionAftercol))
  {
    return positionAftercol;
  }
  ErrorHandlerFn("_enum_constraint",
    "col",
    EverParseErrorReasonOfResult(positionAftercol),
    EverParseGetValidatorErrorKind(positionAftercol),
    Ctxt,
    Input,
    StartPosition);
  return positionAftercol;
}

