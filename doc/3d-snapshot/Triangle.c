

#include "Triangle.h"

static uint8_t
ValidateCoreTriangle(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
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
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
    resultAfterTriangle = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterTriangle = res;
  }
  if (resultAfterTriangle == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterTriangle;
  }
  ErrorHandlerFn("_triangle",
    "a",
    EverParsePulseInternalErrorReasonOfResult(resultAfterTriangle),
    resultAfterTriangle == 0U || (resultAfterTriangle >= 2U && resultAfterTriangle <= 8U) ? (uint64_t)(uint32_t)resultAfterTriangle
                                                                                          : 15ULL,
    Ctxt,
    SlBase,
    startPositionTriangle);
  return resultAfterTriangle;
}

uint64_t
TriangleValidateTriangle(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreTriangle(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

