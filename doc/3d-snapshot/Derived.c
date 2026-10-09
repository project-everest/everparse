

#include "Derived.h"

static uint8_t
ValidateCoreTriple(
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
    resultAfterTriple = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterTriple = res;
  }
  if (resultAfterTriple == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterTriple;
  }
  ErrorHandlerFn("_Triple",
    "pair",
    EverParsePulseInternalErrorReasonOfResult(resultAfterTriple),
    resultAfterTriple == 0U || (resultAfterTriple >= 2U && resultAfterTriple <= 8U) ? (uint64_t)(uint32_t)resultAfterTriple
                                                                                    : 15ULL,
    Ctxt,
    SlBase,
    startPositionTriple);
  return resultAfterTriple;
}

uint64_t
DerivedValidateTriple(
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
  uint8_t status = ValidateCoreTriple(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreQuad(
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
    resultAfterQuad = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterQuad = res;
  }
  if (resultAfterQuad == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterQuad;
  }
  ErrorHandlerFn("_Quad",
    "_12",
    EverParsePulseInternalErrorReasonOfResult(resultAfterQuad),
    resultAfterQuad == 0U || (resultAfterQuad >= 2U && resultAfterQuad <= 8U) ? (uint64_t)(uint32_t)resultAfterQuad
                                                                              : 15ULL,
    Ctxt,
    SlBase,
    startPositionQuad);
  return resultAfterQuad;
}

uint64_t
DerivedValidateQuad(
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
  uint8_t status = ValidateCoreQuad(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

