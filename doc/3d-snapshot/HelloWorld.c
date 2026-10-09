

#include "HelloWorld.h"

#include "EverParse.h"

uint8_t
HelloWorldValidatePoint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartPoint = (uint64_t)p1;
  uint64_t startPositionPoint = fieldStartPoint;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterPoint;
  size_t consumed;
  size_t p;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
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
    resultAfterPoint = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterPoint = res;
  }
  if (resultAfterPoint == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterPoint;
  }
  ErrorHandlerFn("_point",
    "x",
    EverParseErrorReasonOfResult(resultAfterPoint),
    resultAfterPoint,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    startPositionPoint);
  return resultAfterPoint;
}

