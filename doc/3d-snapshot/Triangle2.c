

#include "Triangle2.h"

#include "EverParse.h"

uint8_t
Triangle2ValidateTriangle(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field corners */
  size_t p1 = *SlPos;
  uint64_t fieldStartTriangle = (uint64_t)p1;
  uint64_t startPositionTriangle = fieldStartTriangle;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)12U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterTriangle;
  size_t consumed;
  size_t p;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)12U;
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
    resultAfterTriangle = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterTriangle = res;
  }
  if (resultAfterTriangle == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterTriangle;
  }
  ErrorHandlerFn("_triangle",
    "corners",
    EverParseErrorReasonOfResult(resultAfterTriangle),
    resultAfterTriangle,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    startPositionTriangle);
  return resultAfterTriangle;
}

