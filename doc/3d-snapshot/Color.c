

#include "Color.h"

uint64_t
ColorValidateColoredPoint(
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
  /* Validating field col */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAftercol_refinement;
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
  uint64_t positionAfterColoredPoint;
  if (EverParseIsError(positionAftercol_refinement))
  {
    positionAfterColoredPoint = positionAftercol_refinement;
  }
  else
  {
    /* reading field_value */
    uint32_t col_refinement = Load32Le(Input + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN
    col_refinementConstraintIsOk =
      COLOR_RED == col_refinement || COLOR_GREEN == col_refinement || COLOR_BLUE == col_refinement;
    /* end: checking constraint */
    positionAfterColoredPoint =
      EverParseCheckConstraintOk(col_refinementConstraintIsOk,
        positionAftercol_refinement);
  }
  uint64_t positionAftercol_refinement0;
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    positionAftercol_refinement0 = positionAfterColoredPoint;
  }
  else
  {
    ErrorHandlerFn("_coloredPoint",
      "col.refinement",
      EverParseErrorReasonOfResult(positionAfterColoredPoint),
      EverParseGetValidatorErrorKind(positionAfterColoredPoint),
      Ctxt,
      Input,
      StartPosition);
    positionAftercol_refinement0 = positionAfterColoredPoint;
  }
  if (EverParseIsError(positionAftercol_refinement0))
  {
    return positionAftercol_refinement0;
  }
  BOOLEAN hasBytes = 8ULL <= (InputLength - positionAftercol_refinement0);
  if (hasBytes)
  {
    return positionAftercol_refinement0 + 8ULL;
  }
  return
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
      positionAftercol_refinement0);
}

