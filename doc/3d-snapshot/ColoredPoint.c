

#include "ColoredPoint.h"

uint64_t
ColoredPointValidateColoredPoint1(
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
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  BOOLEAN hasBytes = 5ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 5ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

uint64_t
ColoredPointValidateColoredPoint2(
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
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  BOOLEAN hasBytes = 5ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 5ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

