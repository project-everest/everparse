

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
  BOOLEAN hasBytesForCol = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterCol0;
  uint64_t positionAfterCol;
  uint32_t col;
  BOOLEAN colConstraintIsOk;
  uint64_t positionAfterCheckedCol;
  BOOLEAN hasBytesForX_refinement;
  uint64_t positionAfterX_refinement;
  uint64_t positionAfterX_refinement0;
  uint32_t x_refinement;
  BOOLEAN x_refinementConstraintIsOk;
  if (hasBytesForCol)
  {
    positionAfterCol0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterCol0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterCol0))
  {
    positionAfterCol = positionAfterCol0;
  }
  else
  {
    col = Load32Le(Input + (uint32_t)StartPosition);
    colConstraintIsOk =
      col == ENUMCONSTRAINT_RED || col == ENUMCONSTRAINT_GREEN || col == ENUMCONSTRAINT_BLUE;
    positionAfterCheckedCol = EverParseCheckConstraintOk(colConstraintIsOk, positionAfterCol0);
    if (EverParseIsError(positionAfterCheckedCol))
    {
      positionAfterCol = positionAfterCheckedCol;
    }
    else
    {
      /* Validating field x */
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      hasBytesForX_refinement = (InputLength - positionAfterCheckedCol) >= 4ULL;
      if (hasBytesForX_refinement)
      {
        positionAfterX_refinement = positionAfterCheckedCol + 4ULL;
      }
      else
      {
        positionAfterX_refinement =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedCol);
      }
      if (EverParseIsError(positionAfterX_refinement))
      {
        positionAfterX_refinement0 = positionAfterX_refinement;
      }
      else
      {
        /* reading field_value */
        x_refinement = Load32Le(Input + (uint32_t)positionAfterCheckedCol);
        /* start: checking constraint */
        x_refinementConstraintIsOk = x_refinement == 0U || col == ENUMCONSTRAINT_GREEN;
        /* end: checking constraint */
        positionAfterX_refinement0 =
          EverParseCheckConstraintOk(x_refinementConstraintIsOk,
            positionAfterX_refinement);
      }
      if (EverParseIsSuccess(positionAfterX_refinement0))
      {
        positionAfterCol = positionAfterX_refinement0;
      }
      else
      {
        ErrorHandlerFn("_enum_constraint",
          "x.refinement",
          EverParseErrorReasonOfResult(positionAfterX_refinement0),
          EverParseGetValidatorErrorKind(positionAfterX_refinement0),
          Ctxt,
          Input,
          positionAfterCheckedCol);
        positionAfterCol = positionAfterX_refinement0;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterCol))
  {
    return positionAfterCol;
  }
  ErrorHandlerFn("_enum_constraint",
    "col",
    EverParseErrorReasonOfResult(positionAfterCol),
    EverParseGetValidatorErrorKind(positionAfterCol),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterCol;
}

