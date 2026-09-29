

#include "Color.h"

#include "EverParse.h"

uint64_t
ColorValidateColoredPoint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field col */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAftercol_refinement;
  uint64_t positionAftercol_refinement0;
  uint32_t col_refinement;
  BOOLEAN col_refinementConstraintIsOk;
  uint64_t positionAftercol_refinement1;
  BOOLEAN hasBytes;
  uint64_t res;
  uint64_t positionAfterx;
  if (hasBytes0)
  {
    positionAftercol_refinement = StartPosition + 4ULL;
  }
  else
  {
    positionAftercol_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAftercol_refinement))
  {
    positionAftercol_refinement0 = positionAftercol_refinement;
  }
  else
  {
    /* reading field_value */
    col_refinement = Load32Le(Input + (uint32_t)StartPosition);
    /* start: checking constraint */
    col_refinementConstraintIsOk =
      COLOR_RED == col_refinement || COLOR_GREEN == col_refinement || COLOR_BLUE == col_refinement;
    /* end: checking constraint */
    positionAftercol_refinement0 =
      EverParseCheckConstraintOk(col_refinementConstraintIsOk,
        positionAftercol_refinement);
  }
  if (EverParseIsSuccess(positionAftercol_refinement0))
  {
    positionAftercol_refinement1 = positionAftercol_refinement0;
  }
  else
  {
    ErrorHandlerFn("_coloredPoint",
      "col.refinement",
      EverParseErrorReasonOfResult(positionAftercol_refinement0),
      EverParseGetValidatorErrorKind(positionAftercol_refinement0),
      Ctxt,
      Input,
      StartPosition);
    positionAftercol_refinement1 = positionAftercol_refinement0;
  }
  if (EverParseIsError(positionAftercol_refinement1))
  {
    return positionAftercol_refinement1;
  }
  hasBytes = (InputLength - positionAftercol_refinement1) >= 8ULL;
  if (hasBytes)
  {
    res = positionAftercol_refinement1 + 8ULL;
  }
  else
  {
    res =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftercol_refinement1);
  }
  positionAfterx = res;
  if (EverParseIsSuccess(positionAfterx))
  {
    return positionAfterx;
  }
  ErrorHandlerFn("_coloredPoint",
    "x",
    EverParseErrorReasonOfResult(positionAfterx),
    EverParseGetValidatorErrorKind(positionAfterx),
    Ctxt,
    Input,
    positionAftercol_refinement1);
  return positionAfterx;
}

