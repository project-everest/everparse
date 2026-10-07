

#include "Align.h"

#include "EverParse.h"

uint8_t
AlignValidateColoredPoint1(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartColoredPoint1 = (uint64_t)p1;
  uint64_t startPositionColoredPoint1 = fieldStartColoredPoint1;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)6U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterColoredPoint1;
  size_t consumed;
  size_t p;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)6U;
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
    resultAfterColoredPoint1 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterColoredPoint1 = res;
  }
  if (resultAfterColoredPoint1 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterColoredPoint1;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParseErrorReasonOfResult(resultAfterColoredPoint1),
    resultAfterColoredPoint1,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    startPositionColoredPoint1);
  return resultAfterColoredPoint1;
}

