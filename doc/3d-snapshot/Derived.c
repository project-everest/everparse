

#include "Derived.h"

#include "EverParse.h"

uint8_t
DerivedValidateTriple(
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
  uint64_t fieldStartTriple = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)12U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterTriple;
  size_t consumed;
  size_t p2;
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
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterTriple = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterTriple = res;
  }
  if (resultAfterTriple == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterTriple;
  }
  ErrorHandlerFn("_Triple",
    "pair",
    EverParseErrorReasonOfResult(resultAfterTriple),
    resultAfterTriple,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartTriple);
  return resultAfterTriple;
}

uint8_t
DerivedValidateQuad(
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
  uint64_t fieldStartQuad = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)16U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterQuad;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)16U;
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
    resultAfterQuad = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterQuad = res;
  }
  if (resultAfterQuad == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterQuad;
  }
  ErrorHandlerFn("_Quad",
    "_12",
    EverParseErrorReasonOfResult(resultAfterQuad),
    resultAfterQuad,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartQuad);
  return resultAfterQuad;
}

