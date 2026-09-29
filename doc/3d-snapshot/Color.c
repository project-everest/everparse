

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
  uint64_t positionAfterCol_refinement;
  uint64_t positionAfterCol_refinement0;
  uint32_t col_refinement;
  BOOLEAN col_refinementConstraintIsOk;
  uint64_t positionAfterCol_refinement1;
  BOOLEAN hasBytes;
  uint64_t res;
  uint64_t positionAfterX;
  if (hasBytes0)
  {
    positionAfterCol_refinement = StartPosition + 4ULL;
  }
  else
  {
    positionAfterCol_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterCol_refinement))
  {
    positionAfterCol_refinement0 = positionAfterCol_refinement;
  }
  else
  {
    /* reading field_value */
    col_refinement = Load32Le(Input + (uint32_t)StartPosition);
    /* start: checking constraint */
    col_refinementConstraintIsOk =
      COLOR_RED == col_refinement || COLOR_GREEN == col_refinement || COLOR_BLUE == col_refinement;
    /* end: checking constraint */
    positionAfterCol_refinement0 =
      EverParseCheckConstraintOk(col_refinementConstraintIsOk,
        positionAfterCol_refinement);
  }
  if (EverParseIsSuccess(positionAfterCol_refinement0))
  {
    positionAfterCol_refinement1 = positionAfterCol_refinement0;
  }
  else
  {
    ErrorHandlerFn("_coloredPoint",
      "col.refinement",
      EverParseErrorReasonOfResult(positionAfterCol_refinement0),
      EverParseGetValidatorErrorKind(positionAfterCol_refinement0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterCol_refinement1 = positionAfterCol_refinement0;
  }
  if (EverParseIsError(positionAfterCol_refinement1))
  {
    return positionAfterCol_refinement1;
  }
  hasBytes = (InputLength - positionAfterCol_refinement1) >= 8ULL;
  if (hasBytes)
  {
    res = positionAfterCol_refinement1 + 8ULL;
  }
  else
  {
    res =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterCol_refinement1);
  }
  positionAfterX = res;
  if (EverParseIsSuccess(positionAfterX))
  {
    return positionAfterX;
  }
  ErrorHandlerFn("_coloredPoint",
    "x",
    EverParseErrorReasonOfResult(positionAfterX),
    EverParseGetValidatorErrorKind(positionAfterX),
    Ctxt,
    Input,
    positionAfterCol_refinement1);
  return positionAfterX;
}

