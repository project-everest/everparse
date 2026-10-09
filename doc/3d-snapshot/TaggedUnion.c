

#include "TaggedUnion.h"

inline uint8_t
TaggedUnionValidateCoreIntPayload(
  uint32_t Size,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos0;
  size_t p3;
  uint64_t viewStart;
  size_t fieldOff;
  uint64_t startPos;
  size_t p00;
  size_t p10;
  size_t rem0;
  BOOLEAN hasBytes0;
  uint8_t res0;
  uint8_t res10;
  size_t consumed0;
  size_t p20;
  size_t p_;
  size_t pos1;
  size_t p4;
  uint64_t viewStart0;
  size_t fieldOff0;
  uint64_t startPos0;
  size_t p01;
  size_t p11;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res2;
  uint8_t res11;
  size_t consumed1;
  size_t p21;
  size_t p_0;
  size_t pos2;
  size_t p5;
  uint64_t viewStart1;
  size_t fieldOff1;
  uint64_t startPos1;
  size_t p0;
  size_t p12;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res3;
  uint8_t res12;
  size_t consumed2;
  size_t p2;
  size_t p_1;
  size_t pos;
  size_t p;
  uint64_t viewStart2;
  size_t fieldOff2;
  uint64_t startPos2;
  uint8_t res;
  uint8_t res1;
  size_t consumed;
  size_t p1;
  size_t p_2;
  if (Size == (uint32_t)TAGGEDUNION_SIZE8)
  {
    pos0 = (size_t)0U;
    /* Validating field value8 */
    p3 = SlPos[0U];
    viewStart = (uint64_t)p3;
    fieldOff = pos0;
    startPos = viewStart + (uint64_t)fieldOff;
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    p00 = pos0;
    p10 = SlPos[0U];
    rem0 = SlLen - p10;
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
      res10 = res0;
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
      res10 = res0;
    }
    if (res10 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed0 = pos0;
      p20 = SlPos[0U];
      p_ = p20 + consumed0;
      SlPos[0U] = p_;
      return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    return res10;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE16)
  {
    pos1 = (size_t)0U;
    /* Validating field value16 */
    p4 = SlPos[0U];
    viewStart0 = (uint64_t)p4;
    fieldOff0 = pos1;
    startPos0 = viewStart0 + (uint64_t)fieldOff0;
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    p01 = pos1;
    p11 = SlPos[0U];
    rem1 = SlLen - p11;
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
      res11 = res2;
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
      res11 = res2;
    }
    if (res11 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed1 = pos1;
      p21 = SlPos[0U];
      p_0 = p21 + consumed1;
      SlPos[0U] = p_0;
      return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    return res11;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE32)
  {
    pos2 = (size_t)0U;
    /* Validating field value32 */
    p5 = SlPos[0U];
    viewStart1 = (uint64_t)p5;
    fieldOff1 = pos2;
    startPos1 = viewStart1 + (uint64_t)fieldOff1;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p0 = pos2;
    p12 = SlPos[0U];
    rem = SlLen - p12;
    hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
    if (hasBytes)
    {
      pos2 = p0 + (size_t)4U;
      res3 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res3 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res3 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      res12 = res3;
    }
    else
    {
      ErrorHandlerFn("_int_payload",
        "value32",
        EverParsePulseInternalErrorReasonOfResult(res3),
        res3 == 0U || (res3 >= 2U && res3 <= 8U) ? (uint64_t)(uint32_t)res3 : 15ULL,
        Ctxt,
        SlBase,
        startPos1);
      res12 = res3;
    }
    if (res12 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed2 = pos2;
      p2 = SlPos[0U];
      p_1 = p2 + consumed2;
      SlPos[0U] = p_1;
      return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    return res12;
  }
  pos = (size_t)0U;
  p = SlPos[0U];
  viewStart2 = (uint64_t)p;
  fieldOff2 = pos;
  startPos2 = viewStart2 + (uint64_t)fieldOff2;
  res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_IMPOSSIBLE;
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res1 = res;
  }
  else
  {
    ErrorHandlerFn("_int_payload",
      "_x_17",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos2);
    res1 = res;
  }
  if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p1 = SlPos[0U];
    p_2 = p1 + consumed;
    SlPos[0U] = p_2;
    return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  return res1;
}

uint8_t
TaggedUnionValidateCoreInteger(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos = (size_t)0U;
  size_t p = SlPos[0U];
  uint64_t viewStart = (uint64_t)p;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t res;
  uint8_t resultAftersize;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  size_t pos_;
  uint8_t first1;
  size_t pos_1;
  uint8_t first2;
  uint8_t first3;
  uint32_t n;
  uint32_t bfirst;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t size;
  size_t p2;
  uint64_t fieldStartInteger;
  uint8_t resultAfterInteger;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAftersize = res;
  }
  else
  {
    ErrorHandlerFn("_integer",
      "size",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAftersize = res;
  }
  if (resultAftersize == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)4U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    first = sub[0U];
    pos_ = (size_t)2U;
    first1 = sub[1U];
    pos_1 = pos_ + (size_t)1U;
    first2 = sub[pos_];
    first3 = sub[pos_1];
    n = (uint32_t)first3;
    bfirst = (uint32_t)first2;
    n1 = bfirst + n * 256U;
    bfirst1 = (uint32_t)first1;
    n2 = bfirst1 + n1 * 256U;
    bfirst2 = (uint32_t)first;
    size = bfirst2 + n2 * 256U;
    /* Validating field payload */
    p2 = SlPos[0U];
    fieldStartInteger = (uint64_t)p2;
    resultAfterInteger =
      TaggedUnionValidateCoreIntPayload(size,
        Ctxt,
        ErrorHandlerFn,
        SlBase,
        SlLen,
        SlPos);
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
      fieldStartInteger);
    return resultAfterInteger;
  }
  return resultAftersize;
}

uint64_t
TaggedUnionValidateInteger(
  uint8_t *Ctxt,
  void
  (*Handler)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = TaggedUnionValidateCoreInteger(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

