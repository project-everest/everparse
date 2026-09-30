

#include "Align.h"

#include "EverParse.h"

uint64_t
AlignValidateColoredPoint1(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytesForColorAlignmentPadding0pt = (InputLength - StartPosition) >= 6ULL;
  uint64_t resForColorAlignmentPadding0pt;
  uint64_t positionAfterColorOrError;
  if (hasBytesForColorAlignmentPadding0pt)
  {
    resForColorAlignmentPadding0pt = StartPosition + 6ULL;
  }
  else
  {
    resForColorAlignmentPadding0pt =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterColorOrError = resForColorAlignmentPadding0pt;
  if (EverParseIsSuccess(positionAfterColorOrError))
  {
    return positionAfterColorOrError;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParseErrorReasonOfResult(positionAfterColorOrError),
    EverParseGetValidatorErrorKind(positionAfterColorOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColorOrError;
}

