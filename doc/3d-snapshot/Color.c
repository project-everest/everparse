

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
  BOOLEAN hasBytesForCol_refinement = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterCol_refinement;
  uint64_t positionAfterCol_refinementOrError;
  uint32_t col_refinement;
  BOOLEAN col_refinementConstraintIsOk;
  uint64_t positionAfterCol_refinement0;
  BOOLEAN hasBytesForXY;
  uint64_t resForXY;
  uint64_t positionAfterXOrError;
  if (hasBytesForCol_refinement)
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
    positionAfterCol_refinementOrError = positionAfterCol_refinement;
  }
  else
  {
    /* reading field_value */
    col_refinement = Load32Le(Input + (uint32_t)StartPosition);
    /* start: checking constraint */
    col_refinementConstraintIsOk =
      COLOR_RED == col_refinement || COLOR_GREEN == col_refinement || COLOR_BLUE == col_refinement;
    /* end: checking constraint */
    positionAfterCol_refinementOrError =
      EverParseCheckConstraintOk(col_refinementConstraintIsOk,
        positionAfterCol_refinement);
  }
  if (EverParseIsSuccess(positionAfterCol_refinementOrError))
  {
    positionAfterCol_refinement0 = positionAfterCol_refinementOrError;
  }
  else
  {
    ErrorHandlerFn("_coloredPoint",
      "col.refinement",
      EverParseErrorReasonOfResult(positionAfterCol_refinementOrError),
      EverParseGetValidatorErrorKind(positionAfterCol_refinementOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterCol_refinement0 = positionAfterCol_refinementOrError;
  }
  if (EverParseIsError(positionAfterCol_refinement0))
  {
    return positionAfterCol_refinement0;
  }
  hasBytesForXY = (InputLength - positionAfterCol_refinement0) >= 8ULL;
  if (hasBytesForXY)
  {
    resForXY = positionAfterCol_refinement0 + 8ULL;
  }
  else
  {
    resForXY =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterCol_refinement0);
  }
  positionAfterXOrError = resForXY;
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    return positionAfterXOrError;
  }
  ErrorHandlerFn("_coloredPoint",
    "x",
    EverParseErrorReasonOfResult(positionAfterXOrError),
    EverParseGetValidatorErrorKind(positionAfterXOrError),
    Ctxt,
    Input,
    positionAfterCol_refinement0);
  return positionAfterXOrError;
}

