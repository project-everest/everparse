

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
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 6ULL;
  uint64_t res;
  uint64_t positionAfterColoredPoint1;
  if (hasBytes)
  {
    res = StartPosition + 6ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterColoredPoint1 = res;
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    return positionAfterColoredPoint1;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParseErrorReasonOfResult(positionAfterColoredPoint1),
    EverParseGetValidatorErrorKind(positionAfterColoredPoint1),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterColoredPoint1;
}

