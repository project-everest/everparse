

#include "PointArch_32_64.h"

#include "EverParse.h"

static inline uint8_t
ValidateInt(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos0;
  size_t p1;
  uint64_t viewStart;
  size_t fieldOff;
  uint64_t startPos;
  size_t p00;
  size_t p2;
  size_t rem0;
  BOOLEAN hasBytes0;
  uint8_t res0;
  uint8_t res1;
  size_t consumed0;
  size_t p3;
  size_t p_;
  size_t pos;
  size_t p4;
  uint64_t viewStart0;
  size_t fieldOff0;
  uint64_t startPos0;
  size_t p0;
  size_t p5;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res2;
  uint8_t res;
  size_t consumed;
  size_t p;
  size_t p_0;
  #if ARCH64
  {
    KRML_MAYBE_UNUSED_VAR(viewStart0);
    KRML_MAYBE_UNUSED_VAR(startPos0);
    KRML_MAYBE_UNUSED_VAR(res2);
    KRML_MAYBE_UNUSED_VAR(res);
    KRML_MAYBE_UNUSED_VAR(rem);
    KRML_MAYBE_UNUSED_VAR(pos);
    KRML_MAYBE_UNUSED_VAR(p_0);
    KRML_MAYBE_UNUSED_VAR(p5);
    KRML_MAYBE_UNUSED_VAR(p4);
    KRML_MAYBE_UNUSED_VAR(p0);
    KRML_MAYBE_UNUSED_VAR(p);
    KRML_MAYBE_UNUSED_VAR(hasBytes);
    KRML_MAYBE_UNUSED_VAR(fieldOff0);
    KRML_MAYBE_UNUSED_VAR(consumed);
    pos0 = (size_t)0U;
    /* Validating field x */
    p1 = *SlPos;
    viewStart = (uint64_t)p1;
    fieldOff = pos0;
    startPos = viewStart + (uint64_t)fieldOff;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p00 = pos0;
    p2 = *SlPos;
    rem0 = SlLen - p2;
    hasBytes0 = p00 <= rem0 && (size_t)8U <= (rem0 - p00);
    if (hasBytes0)
    {
      pos0 = p00 + (size_t)8U;
      res0 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res0 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      res1 = res0;
    }
    else
    {
      ErrorHandlerFn("_INT",
        "x",
        EverParseErrorReasonOfResult(res0),
        res0,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        startPos);
      res1 = res0;
    }
    if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      consumed0 = pos0;
      p3 = *SlPos;
      p_ = p3 + consumed0;
      *SlPos = p_;
      return EVERPARSE_VALIDATOR_SUCCESS;
    }
    return res1;
  }
  #else
  {
    KRML_MAYBE_UNUSED_VAR(viewStart);
    KRML_MAYBE_UNUSED_VAR(startPos);
    KRML_MAYBE_UNUSED_VAR(res1);
    KRML_MAYBE_UNUSED_VAR(res0);
    KRML_MAYBE_UNUSED_VAR(rem0);
    KRML_MAYBE_UNUSED_VAR(pos0);
    KRML_MAYBE_UNUSED_VAR(p_);
    KRML_MAYBE_UNUSED_VAR(p3);
    KRML_MAYBE_UNUSED_VAR(p2);
    KRML_MAYBE_UNUSED_VAR(p1);
    KRML_MAYBE_UNUSED_VAR(p00);
    KRML_MAYBE_UNUSED_VAR(hasBytes0);
    KRML_MAYBE_UNUSED_VAR(fieldOff);
    KRML_MAYBE_UNUSED_VAR(consumed0);
    pos = (size_t)0U;
    /* Validating field x */
    p4 = *SlPos;
    viewStart0 = (uint64_t)p4;
    fieldOff0 = pos;
    startPos0 = viewStart0 + (uint64_t)fieldOff0;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p0 = pos;
    p5 = *SlPos;
    rem = SlLen - p5;
    hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
    if (hasBytes)
    {
      pos = p0 + (size_t)4U;
      res2 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res2 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res2 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      res = res2;
    }
    else
    {
      ErrorHandlerFn("_INT",
        "x",
        EverParseErrorReasonOfResult(res2),
        res2,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        startPos0);
      res = res2;
    }
    if (res == EVERPARSE_VALIDATOR_SUCCESS)
    {
      consumed = pos;
      p = *SlPos;
      p_0 = p + consumed;
      *SlPos = p_0;
      return EVERPARSE_VALIDATOR_SUCCESS;
    }
    return res;
  }
  #endif
}

uint8_t
PointArch3264ValidatePoint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field x */
  size_t p0 = *SlPos;
  uint64_t fieldStartPoint = (uint64_t)p0;
  uint64_t startPositionPoint = fieldStartPoint;
  uint8_t resultAfterPoint = ValidateInt(Ctxt, ErrorHandlerFn, SlBase, SlLen, SlPos);
  uint8_t resultAfterx;
  size_t p;
  uint64_t fieldStartPoint0;
  uint64_t startPositionPoint0;
  uint8_t resultAfterPoint0;
  if (resultAfterPoint == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterx = resultAfterPoint;
  }
  else
  {
    ErrorHandlerFn("_POINT",
      "x",
      EverParseErrorReasonOfResult(resultAfterPoint),
      resultAfterPoint,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionPoint);
    resultAfterx = resultAfterPoint;
  }
  if (resultAfterx == EVERPARSE_VALIDATOR_SUCCESS)
  {
    /* Validating field y */
    p = *SlPos;
    fieldStartPoint0 = (uint64_t)p;
    startPositionPoint0 = fieldStartPoint0;
    resultAfterPoint0 = ValidateInt(Ctxt, ErrorHandlerFn, SlBase, SlLen, SlPos);
    if (resultAfterPoint0 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterPoint0;
    }
    ErrorHandlerFn("_POINT",
      "y",
      EverParseErrorReasonOfResult(resultAfterPoint0),
      resultAfterPoint0,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionPoint0);
    return resultAfterPoint0;
  }
  return resultAfterx;
}

