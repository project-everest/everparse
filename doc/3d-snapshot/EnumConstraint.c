

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
  uint64_t positionAfterCol;
  uint64_t positionAfterColOrError;
  uint32_t col;
  BOOLEAN colConstraintIsOk;
  uint64_t positionAfterCheckedCol;
  BOOLEAN hasBytesForX_refinement;
  uint64_t positionAfterX_refinement;
  uint64_t positionAfterX_refinementOrError;
  uint32_t x_refinement;
  BOOLEAN x_refinementConstraintIsOk;
  if (hasBytesForCol)
  {
    positionAfterCol = StartPosition + 4ULL;
  }
  else
  {
    positionAfterCol =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterCol))
  {
    positionAfterColOrError = positionAfterCol;
  }
  else
  {
    col = Load32Le(Input + (uint32_t)StartPosition);
    colConstraintIsOk =
      col == ENUMCONSTRAINT_RED || col == ENUMCONSTRAINT_GREEN || col == ENUMCONSTRAINT_BLUE;
    positionAfterCheckedCol = EverParseCheckConstraintOk(colConstraintIsOk, positionAfterCol);
    if (EverParseIsError(positionAfterCheckedCol))
    {
      positionAfterColOrError = positionAfterCheckedCol;
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
        positionAfterX_refinementOrError = positionAfterX_refinement;
      }
      else
      {
        /* reading field_value */
        x_refinement = Load32Le(Input + (uint32_t)positionAfterCheckedCol);
        /* start: checking constraint */
        x_refinementConstraintIsOk = x_refinement == 0U || col == ENUMCONSTRAINT_GREEN;
        /* end: checking constraint */
        positionAfterX_refinementOrError =
          EverParseCheckConstraintOk(x_refinementConstraintIsOk,
            positionAfterX_refinement);
      }
      if (EverParseIsSuccess(positionAfterX_refinementOrError))
      {
        positionAfterColOrError = positionAfterX_refinementOrError;
      }
      else
      {
        ErrorHandlerFn("_enum_constraint",
          "x.refinement",
          EverParseErrorReasonOfResult(positionAfterX_refinementOrError),
          EverParseGetValidatorErrorKind(positionAfterX_refinementOrError),
          Ctxt,
          Input,
          positionAfterCheckedCol);
        positionAfterColOrError = positionAfterX_refinementOrError;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterColOrError))
  {
    return positionAfterColOrError;
  }
  ErrorHandlerFn("_enum_constraint",
    "col",
    EverParseErrorReasonOfResult(positionAfterColOrError),
    EverParseGetValidatorErrorKind(positionAfterColOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColOrError;
}

