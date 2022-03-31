

#include "Color.h"



uint64_t
ColorValidateColoredPoint(
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
  /* Validating field col */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAftercol_refinement;
  if (hasBytes0)
  {
    positionAftercol_refinement = StartPosition + (uint64_t)4U;
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
      COLOR_RED
      == col_refinement
      || COLOR_GREEN == col_refinement || COLOR_BLUE == col_refinement;
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
    Err("_coloredPoint",
      "col.refinement",
      EverParseErrorReasonOfResult(positionAfterColoredPoint),
      Ctxt,
      Input,
      StartPosition);
    positionAftercol_refinement0 = positionAfterColoredPoint;
  }
  if (EverParseIsError(positionAftercol_refinement0))
  {
    return positionAftercol_refinement0;
  }
  /* Validating field x */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes1 = (uint64_t)4U <= (InputLength - positionAftercol_refinement0);
  uint64_t positionAfterColoredPoint0;
  if (hasBytes1)
  {
    positionAfterColoredPoint0 = positionAftercol_refinement0 + (uint64_t)4U;
  }
  else
  {
    positionAfterColoredPoint0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftercol_refinement0);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterColoredPoint0))
  {
    res = positionAfterColoredPoint0;
  }
  else
  {
    Err("_coloredPoint",
      "x",
      EverParseErrorReasonOfResult(positionAfterColoredPoint0),
      Ctxt,
      Input,
      positionAftercol_refinement0);
    res = positionAfterColoredPoint0;
  }
  uint64_t positionAfterx = res;
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Validating field y */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - positionAfterx);
  uint64_t positionAfterColoredPoint1;
  if (hasBytes)
  {
    positionAfterColoredPoint1 = positionAfterx + (uint64_t)4U;
  }
  else
  {
    positionAfterColoredPoint1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterx);
  }
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    return positionAfterColoredPoint1;
  }
  Err("_coloredPoint",
    "y",
    EverParseErrorReasonOfResult(positionAfterColoredPoint1),
    Ctxt,
    Input,
    positionAfterx);
  return positionAfterColoredPoint1;
}

