

#include "Base.h"

#include "EverParse.h"

uint8_t
BaseValidateUlong(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos,
  size_t *Pos
)
{
  size_t p = SlPos[0U];
  uint64_t viewStart = (uint64_t)p;
  size_t fieldOff = Pos[0U];
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = Pos[0U];
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t res;
  if (hasBytes)
  {
    Pos[0U] = p0 + (size_t)4U;
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return res;
  }
  ErrorHandlerFn("___ULONG",
    "missing",
    EverParseErrorReasonOfResult(res),
    res,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    startPos);
  return res;
}

uint8_t
BaseValidatePair(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p = SlPos[0U];
  uint64_t fieldStartPair = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterPair;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)8U;
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterPair = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterPair = res;
  }
  if (resultAfterPair == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterPair;
  }
  ErrorHandlerFn("_Pair",
    "first",
    EverParseErrorReasonOfResult(resultAfterPair),
    resultAfterPair,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartPair);
  return resultAfterPair;
}

