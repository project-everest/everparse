

#include "TaggedUnion.h"

static inline uint8_t
ValidateCoreIntPayload(
  uint32_t Size,
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
  size_t pos1;
  size_t p4;
  uint64_t viewStart0;
  size_t fieldOff0;
  uint64_t startPos0;
  size_t p01;
  size_t p5;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res2;
  uint8_t res3;
  size_t consumed1;
  size_t p6;
  size_t p_0;
  size_t pos2;
  size_t p7;
  uint64_t viewStart1;
  size_t fieldOff1;
  uint64_t startPos1;
  size_t p0;
  size_t p8;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res4;
  uint8_t res5;
  size_t consumed2;
  size_t p9;
  size_t p_1;
  size_t pos;
  size_t p10;
  uint64_t viewStart2;
  size_t fieldOff2;
  uint64_t startPos2;
  uint8_t res6;
  uint8_t res;
  size_t consumed;
  size_t p;
  size_t p_2;
  if (Size == (uint32_t)TAGGEDUNION_SIZE8)
  {
    pos0 = (size_t)0U;
    /* Validating field value8 */
    p1 = *SlPos;
    viewStart = (uint64_t)p1;
    fieldOff = pos0;
    startPos = viewStart + (uint64_t)fieldOff;
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    p00 = pos0;
    p2 = *SlPos;
    rem0 = SlLen - p2;
    hasBytes0 = p00 <= rem0 && (size_t)1U <= (rem0 - p00);
    if (hasBytes0)
    {
      pos0 = p00 + (size_t)1U;
      res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      res1 = res0;
    }
    else
    {
      ErrorHandlerFn("_int_payload",
        "value8",
        EverParsePulseInternalErrorReasonOfResult(res0),
        res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
        Ctxt,
        SlBase,
        startPos);
      res1 = res0;
    }
    if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed0 = pos0;
      p3 = *SlPos;
      p_ = p3 + consumed0;
      *SlPos = p_;
      return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    return res1;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE16)
  {
    pos1 = (size_t)0U;
    /* Validating field value16 */
    p4 = *SlPos;
    viewStart0 = (uint64_t)p4;
    fieldOff0 = pos1;
    startPos0 = viewStart0 + (uint64_t)fieldOff0;
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    p01 = pos1;
    p5 = *SlPos;
    rem1 = SlLen - p5;
    hasBytes1 = p01 <= rem1 && (size_t)2U <= (rem1 - p01);
    if (hasBytes1)
    {
      pos1 = p01 + (size_t)2U;
      res2 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res2 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      res3 = res2;
    }
    else
    {
      ErrorHandlerFn("_int_payload",
        "value16",
        EverParsePulseInternalErrorReasonOfResult(res2),
        res2 == 0U || (res2 >= 2U && res2 <= 8U) ? (uint64_t)(uint32_t)res2 : 15ULL,
        Ctxt,
        SlBase,
        startPos0);
      res3 = res2;
    }
    if (res3 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed1 = pos1;
      p6 = *SlPos;
      p_0 = p6 + consumed1;
      *SlPos = p_0;
      return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    return res3;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE32)
  {
    pos2 = (size_t)0U;
    /* Validating field value32 */
    p7 = *SlPos;
    viewStart1 = (uint64_t)p7;
    fieldOff1 = pos2;
    startPos1 = viewStart1 + (uint64_t)fieldOff1;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p0 = pos2;
    p8 = *SlPos;
    rem = SlLen - p8;
    hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
    if (hasBytes)
    {
      pos2 = p0 + (size_t)4U;
      res4 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res4 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res4 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      res5 = res4;
    }
    else
    {
      ErrorHandlerFn("_int_payload",
        "value32",
        EverParsePulseInternalErrorReasonOfResult(res4),
        res4 == 0U || (res4 >= 2U && res4 <= 8U) ? (uint64_t)(uint32_t)res4 : 15ULL,
        Ctxt,
        SlBase,
        startPos1);
      res5 = res4;
    }
    if (res5 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed2 = pos2;
      p9 = *SlPos;
      p_1 = p9 + consumed2;
      *SlPos = p_1;
      return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    return res5;
  }
  pos = (size_t)0U;
  p10 = *SlPos;
  viewStart2 = (uint64_t)p10;
  fieldOff2 = pos;
  startPos2 = viewStart2 + (uint64_t)fieldOff2;
  res6 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_IMPOSSIBLE;
  if (res6 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res = res6;
  }
  else
  {
    ErrorHandlerFn("_int_payload",
      "_x_17",
      EverParsePulseInternalErrorReasonOfResult(res6),
      res6 == 0U || (res6 >= 2U && res6 <= 8U) ? (uint64_t)(uint32_t)res6 : 15ULL,
      Ctxt,
      SlBase,
      startPos2);
    res = res6;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p = *SlPos;
    p_2 = p + consumed;
    *SlPos = p_2;
    return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  return res;
}

static uint8_t
ValidateCoreInteger(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos = (size_t)0U;
  size_t p1 = *SlPos;
  uint64_t viewStart = (uint64_t)p1;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p00 <= rem && (size_t)4U <= (rem - p00);
  uint8_t res0;
  uint8_t resultAftersize;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_;
  uint8_t first;
  size_t pos_1;
  uint8_t first1;
  size_t pos_2;
  uint8_t first2;
  uint8_t first3;
  uint32_t n0;
  uint32_t bfirst0;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n;
  uint32_t bfirst;
  uint32_t res;
  uint32_t size;
  size_t p;
  uint64_t fieldStartInteger;
  uint64_t startPositionInteger;
  uint8_t resultAfterInteger;
  if (hasBytes)
  {
    pos = p00 + (size_t)4U;
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAftersize = res0;
  }
  else
  {
    ErrorHandlerFn("_integer",
      "size",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAftersize = res0;
  }
  if (resultAftersize == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p0 = *SlPos;
    m = p0 + (size_t)4U;
    sub = SlBase + p0;
    pos_ = (size_t)1U;
    first = sub[0U];
    pos_1 = pos_ + (size_t)1U;
    first1 = sub[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first2 = sub[pos_1];
    first3 = sub[pos_2];
    n0 = (uint32_t)first3;
    bfirst0 = (uint32_t)first2;
    n1 = bfirst0 + n0 * 256U;
    bfirst1 = (uint32_t)first1;
    n = bfirst1 + n1 * 256U;
    bfirst = (uint32_t)first;
    res = bfirst + n * 256U;
    *SlPos = m;
    size = res;
    /* Validating field payload */
    p = *SlPos;
    fieldStartInteger = (uint64_t)p;
    startPositionInteger = fieldStartInteger;
    resultAfterInteger = ValidateCoreIntPayload(size, Ctxt, ErrorHandlerFn, SlBase, SlLen, SlPos);
    if (resultAfterInteger == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterInteger;
    }
    ErrorHandlerFn("_integer",
      "payload",
      EverParsePulseInternalErrorReasonOfResult(resultAfterInteger),
      resultAfterInteger == 0U || (resultAfterInteger >= 2U && resultAfterInteger <= 8U) ? (uint64_t)(uint32_t)resultAfterInteger
                                                                                         : 15ULL,
      Ctxt,
      SlBase,
      startPositionInteger);
    return resultAfterInteger;
  }
  return resultAftersize;
}

uint64_t
TaggedUnionValidateInteger(
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
  uint8_t status = ValidateCoreInteger(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

