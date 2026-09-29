

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
  uint64_t positionAftercolor;
  if (hasBytes)
  {
    res = StartPosition + 6ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAftercolor = res;
  if (EverParseIsSuccess(positionAftercolor))
  {
    return positionAftercolor;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParseErrorReasonOfResult(positionAftercolor),
    EverParseGetValidatorErrorKind(positionAftercolor),
    Ctxt,
    Input,
    StartPosition);
  return positionAftercolor;
}

