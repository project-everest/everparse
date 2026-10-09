

#include "Derived.h"

#include "EverParse.h"

uint8_t
DerivedValidateTriple(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartTriple = (uint64_t)p1;
  uint64_t startPositionTriple = fieldStartTriple;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)12U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterTriple;
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
    startPositionTriple);
  return resultAfterTriple;
}

uint8_t
DerivedValidateQuad(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartQuad = (uint64_t)p1;
  uint64_t startPositionQuad = fieldStartQuad;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)16U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterQuad;
  size_t consumed;
  size_t p;
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
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
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
    startPositionQuad);
  return resultAfterQuad;
}

