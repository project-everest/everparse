

#include "SpecializeDep1.h"

#include "SpecializeDep1_ExternalAPI.h"

static inline uint8_t
ValidateCoreUnion(
  uint8_t Tag,
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
  size_t pos;
  size_t p7;
  uint64_t viewStart1;
  size_t fieldOff1;
  uint64_t startPos1;
  size_t p0;
  size_t p8;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res4;
  uint8_t res;
  size_t consumed;
  size_t p;
  size_t p_1;
  if (Tag == 0U)
  {
    pos0 = (size_t)0U;
    /* Validating field case0 */
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
      ErrorHandlerFn("_UNION",
        "case0",
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
  if (Tag == 1U)
  {
    pos1 = (size_t)0U;
    /* Validating field case1 */
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
      ErrorHandlerFn("_UNION",
        "case1",
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
  pos = (size_t)0U;
  /* Validating field other */
  p7 = *SlPos;
  viewStart1 = (uint64_t)p7;
  fieldOff1 = pos;
  startPos1 = viewStart1 + (uint64_t)fieldOff1;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  p0 = pos;
  p8 = *SlPos;
  rem = SlLen - p8;
  hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res4 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res4 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res4 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res = res4;
  }
  else
  {
    ErrorHandlerFn("_UNION",
      "other",
      EverParsePulseInternalErrorReasonOfResult(res4),
      res4 == 0U || (res4 >= 2U && res4 <= 8U) ? (uint64_t)(uint32_t)res4 : 15ULL,
      Ctxt,
      SlBase,
      startPos1);
    res = res4;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p = *SlPos;
    p_1 = p + consumed;
    *SlPos = p_1;
    return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  return res;
}

static void
CopyBytes(
  uint64_t Numbytes,
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  uint64_t rd = *ReadOffset;
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = ProbeAndCopy(Numbytes, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + Numbytes;
    *WriteOffset = wr + Numbytes;
    return;
  }
  *Failed = TRUE;
}

static void
Specialized32ProbeUnion(
  uint8_t Tag,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Err,
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  BOOLEAN hasFailed0;
  BOOLEAN hasFailed1;
  BOOLEAN hasFailed2;
  if (Tag == 0U)
  {
    CopyBytes(1ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
    hasFailed = *Failed;
    if (hasFailed)
    {
      Err(Tn, Fn, "case0", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  else if (Tag == 1U)
  {
    CopyBytes(2ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
    hasFailed0 = *Failed;
    if (hasFailed0)
    {
      Err(Tn, Fn, "case1", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  else
  {
    CopyBytes(4ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
    hasFailed1 = *Failed;
    if (hasFailed1)
    {
      Err(Tn, Fn, "other", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  hasFailed2 = *Failed;
  if (hasFailed2)
  {
    Err(Tn, Fn, "field", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint8_t
ValidateCoreTlv(
  uint16_t Len,
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
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)1U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAftertag;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  uint8_t res1;
  uint8_t tag;
  size_t p3;
  uint64_t fieldStartTlv;
  uint64_t startPositionTlv;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem;
  BOOLEAN hasBytes1;
  uint8_t resultAfterlength;
  uint8_t resultAfterTlv;
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
  uint32_t res2;
  uint32_t length;
  BOOLEAN lengthConstraintIsOk;
  size_t p5;
  uint64_t fieldStartTlv1;
  uint64_t startPositionTlv1;
  size_t nSz;
  size_t p6;
  size_t avail0;
  BOOLEAN hasBytes;
  uint8_t resultAfterTlv0;
  size_t p7;
  size_t tr;
  uint8_t *tb;
  size_t tl;
  size_t *tp;
  uint8_t res;
  BOOLEAN stop;
  BOOLEAN anf0;
  BOOLEAN cond;
  size_t p8;
  size_t avail;
  BOOLEAN hasMore;
  size_t p;
  uint64_t fieldStartTlv2;
  uint64_t startPositionTlv2;
  uint8_t resultAfterTlv1;
  uint8_t r;
  BOOLEAN anf00;
  uint8_t fres;
  if (hasBytes0)
  {
    pos = p00 + (size_t)1U;
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAftertag = res0;
  }
  else
  {
    ErrorHandlerFn("_TLV",
      "tag",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAftertag = res0;
  }
  if (resultAftertag == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)1U;
    sub0 = SlBase + p01;
    res1 = sub0[0U];
    *SlPos = m0;
    tag = res1;
    p3 = *SlPos;
    fieldStartTlv = (uint64_t)p3;
    startPositionTlv = fieldStartTlv;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p4 = *SlPos;
    rem = SlLen - p4;
    hasBytes1 = p02 <= rem && (size_t)4U <= (rem - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)4U;
      resultAfterlength = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterlength = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterlength == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
      res2 = bfirst + n * 256U;
      *SlPos = m;
      length = res2;
      lengthConstraintIsOk = length == (uint32_t)Len;
      if (lengthConstraintIsOk)
      {
        /* Validating field payload */
        p5 = *SlPos;
        fieldStartTlv1 = (uint64_t)p5;
        startPositionTlv1 = fieldStartTlv1;
        nSz = (size_t)(uint32_t)Len;
        p6 = *SlPos;
        avail0 = SlLen - p6;
        hasBytes = nSz <= avail0;
        if (!hasBytes)
        {
          resultAfterTlv0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        else
        {
          p7 = *SlPos;
          tr = p7 + nSz;
          tb = SlBase;
          tl = tr;
          tp = SlPos;
          res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          stop = FALSE;
          anf0 = stop;
          cond = !anf0;
          while (cond)
          {
            p8 = *tp;
            avail = tl - p8;
            hasMore = (size_t)1U <= avail;
            if (!hasMore)
            {
              stop = TRUE;
            }
            else
            {
              p = *tp;
              fieldStartTlv2 = (uint64_t)p;
              startPositionTlv2 = fieldStartTlv2;
              resultAfterTlv1 = ValidateCoreUnion(tag, Ctxt, ErrorHandlerFn, tb, tl, tp);
              if (resultAfterTlv1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
              {
                r = resultAfterTlv1;
              }
              else
              {
                ErrorHandlerFn("_TLV",
                  "payload.element",
                  EverParsePulseInternalErrorReasonOfResult(resultAfterTlv1),
                  resultAfterTlv1 == 0U || (resultAfterTlv1 >= 2U && resultAfterTlv1 <= 8U) ? (uint64_t)(uint32_t)resultAfterTlv1
                                                                                            : 15ULL,
                  Ctxt,
                  tb,
                  startPositionTlv2);
                r = resultAfterTlv1;
              }
              if (!(r == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS))
              {
                res = r;
                stop = TRUE;
              }
            }
            anf00 = stop;
            cond = !anf00;
          }
          fres = res;
          resultAfterTlv0 = fres == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS ? fres : fres;
        }
        if (resultAfterTlv0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          resultAfterTlv = resultAfterTlv0;
        }
        else
        {
          ErrorHandlerFn("_TLV",
            "payload",
            EverParsePulseInternalErrorReasonOfResult(resultAfterTlv0),
            resultAfterTlv0 == 0U || (resultAfterTlv0 >= 2U && resultAfterTlv0 <= 8U) ? (uint64_t)(uint32_t)resultAfterTlv0
                                                                                      : 15ULL,
            Ctxt,
            SlBase,
            startPositionTlv1);
          resultAfterTlv = resultAfterTlv0;
        }
      }
      else
      {
        resultAfterTlv = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
    }
    else
    {
      resultAfterTlv = resultAfterlength;
    }
    if (resultAfterTlv == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterTlv;
    }
    ErrorHandlerFn("_TLV",
      "length",
      EverParsePulseInternalErrorReasonOfResult(resultAfterTlv),
      resultAfterTlv == 0U || (resultAfterTlv >= 2U && resultAfterTlv <= 8U) ? (uint64_t)(uint32_t)resultAfterTlv
                                                                             : 15ULL,
      Ctxt,
      SlBase,
      startPositionTlv);
    return resultAfterTlv;
  }
  return resultAftertag;
}

static void
Specialized32ProbeTlv(
  uint16_t Len,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Err,
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  uint64_t rd = *ReadOffset;
  uint8_t v = ProbeAndReadU8(Failed, rd, Src, Dest);
  BOOLEAN hasFailed = *Failed;
  uint8_t res1;
  BOOLEAN hasFailed0;
  uint64_t wr;
  BOOLEAN ok;
  BOOLEAN hasFailed1;
  BOOLEAN hasFailed2;
  uint64_t ctr;
  BOOLEAN stop;
  BOOLEAN anf0;
  BOOLEAN cond;
  uint64_t c0;
  BOOLEAN hf0;
  uint64_t r0;
  BOOLEAN hasFailed3;
  BOOLEAN hf1;
  uint64_t r1;
  uint64_t bytesRead;
  BOOLEAN anf00;
  if (hasFailed)
  {
    Err(Tn, Fn, Fd, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    res1 = v;
  }
  else
  {
    *ReadOffset = rd + 1ULL;
    res1 = v;
  }
  hasFailed0 = *Failed;
  if (hasFailed0)
  {
    Err(Tn, Fn, "tag", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  wr = *WriteOffset;
  ok = WriteU8(res1, wr, Dest);
  if (ok)
  {
    *WriteOffset = wr + 1ULL;
  }
  else
  {
    *Failed = TRUE;
  }
  hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, "tag", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  CopyBytes(4ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  hasFailed2 = *Failed;
  if (hasFailed2)
  {
    Err(Tn, Fn, "length", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  ctr = (uint64_t)(uint32_t)Len;
  stop = FALSE;
  anf0 = stop;
  cond = !anf0;
  while (cond)
  {
    c0 = ctr;
    hf0 = *Failed;
    if (hf0)
    {
      stop = TRUE;
    }
    else if (c0 == 0ULL)
    {
      stop = TRUE;
    }
    else
    {
      r0 = *ReadOffset;
      Specialized32ProbeUnion(res1, Tn, Fn, Ctxt, Err, ReadOffset, WriteOffset, Failed, Src, Dest);
      hasFailed3 = *Failed;
      if (hasFailed3)
      {
        Err(Tn, Fn, "payload", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      }
      hf1 = *Failed;
      r1 = *ReadOffset;
      if (hf1)
      {
        Err(Tn, Fn, Fd, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
        stop = TRUE;
      }
      else if (r1 == r0)
      {
        Err(Tn, Fn, Fd, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
        *Failed = TRUE;
        stop = TRUE;
      }
      else
      {
        bytesRead = r1 - r0;
        if (c0 < bytesRead)
        {
          Err(Tn, Fn, Fd, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
          *Failed = TRUE;
          stop = TRUE;
        }
        else
        {
          ctr = c0 - bytesRead;
        }
      }
    }
    anf00 = stop;
    cond = !anf00;
  }
}

static inline uint8_t
ValidateCoreWrapper(
  void
  (*ProbeTlv)(
    uint16_t x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    PRIMS_STRING x3,
    uint8_t *x4,
    EVERPARSE_ERROR_HANDLER x5,
    uint64_t *x6,
    uint64_t *x7,
    BOOLEAN *x8,
    uint64_t x9,
    uint64_t x10,
    EVERPARSE_COPY_BUFFER_T x11
  ),
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartWrapper = (uint64_t)p1;
  uint64_t startPositionWrapper = fieldStartWrapper;
  /* Validating field __precondition */
  BOOLEAN preconditionConstraintIsOk = Len > (uint16_t)5U;
  uint8_t resultAfterWrapper;
  size_t p2;
  uint64_t fieldStartWrapper1;
  uint64_t startPositionWrapper1;
  size_t p3;
  uint64_t fieldStarttlv;
  size_t pos;
  size_t p00;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftertlv;
  uint8_t resultAfterWrapper0;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_;
  uint8_t first;
  size_t pos_1;
  uint8_t first1;
  size_t pos_2;
  uint8_t first2;
  size_t pos_3;
  uint8_t first3;
  size_t pos_4;
  uint8_t first4;
  size_t pos_5;
  uint8_t first5;
  size_t pos_6;
  uint8_t first6;
  uint8_t first7;
  uint64_t n0;
  uint64_t bfirst0;
  uint64_t n1;
  uint64_t bfirst1;
  uint64_t n2;
  uint64_t bfirst2;
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n;
  uint64_t bfirst;
  uint64_t res0;
  uint64_t tlv;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionSuccessTlv;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (preconditionConstraintIsOk)
  {
    p2 = *SlPos;
    fieldStartWrapper1 = (uint64_t)p2;
    startPositionWrapper1 = fieldStartWrapper1;
    p3 = *SlPos;
    fieldStarttlv = (uint64_t)p3;
    pos = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p00 = pos;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p00 <= rem && (size_t)8U <= (rem - p00);
    if (hasBytes)
    {
      pos = p00 + (size_t)8U;
      resultAftertlv = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftertlv = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftertlv == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p0 = *SlPos;
      m = p0 + (size_t)8U;
      sub = SlBase + p0;
      pos_ = (size_t)1U;
      first = sub[0U];
      pos_1 = pos_ + (size_t)1U;
      first1 = sub[pos_];
      pos_2 = pos_1 + (size_t)1U;
      first2 = sub[pos_1];
      pos_3 = pos_2 + (size_t)1U;
      first3 = sub[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first4 = sub[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first5 = sub[pos_4];
      pos_6 = pos_5 + (size_t)1U;
      first6 = sub[pos_5];
      first7 = sub[pos_6];
      n0 = (uint64_t)(uint32_t)first7;
      bfirst0 = (uint64_t)(uint32_t)first6;
      n1 = bfirst0 + n0 * 256ULL;
      bfirst1 = (uint64_t)(uint32_t)first5;
      n2 = bfirst1 + n1 * 256ULL;
      bfirst2 = (uint64_t)(uint32_t)first4;
      n3 = bfirst2 + n2 * 256ULL;
      bfirst3 = (uint64_t)(uint32_t)first3;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first2;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first1;
      n = bfirst5 + n5 * 256ULL;
      bfirst = (uint64_t)(uint32_t)first;
      res0 = bfirst + n * 256ULL;
      *SlPos = m;
      tlv = res0;
      src64 = tlv;
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit("_WRAPPER.tlv", (uint64_t)(uint32_t)Len, Output);
      if (ok)
      {
        ProbeTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
          "_WRAPPER",
          "tlv",
          "probe",
          Ctxt,
          ErrorHandlerFn,
          &readOffset,
          &writeOffset,
          &failed,
          src64,
          (uint64_t)(uint32_t)Len,
          Output);
      }
      else
      {
        failed = TRUE;
      }
      wr = writeOffset;
      hasFailed = failed;
      if (hasFailed)
      {
        ErrorHandlerFn("_WRAPPER", "tlv", "probe", 0ULL, Ctxt, EverParseStreamOf(Output), 0ULL);
        b = 0ULL;
      }
      else
      {
        b = wr;
      }
      if (b != 0ULL)
      {
        base = EverParseStreamOf(Output);
        len = (size_t)EverParseStreamLen(Output);
        cursor = (size_t)0U;
        res =
          ValidateCoreTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
            Ctxt,
            ErrorHandlerFn,
            base,
            len,
            &cursor);
        actionSuccessTlv = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("_WRAPPER",
          "tlv",
          EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
            (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                         : 15ULL,
          Ctxt,
          SlBase,
          fieldStarttlv);
        actionSuccessTlv = FALSE;
      }
      resultAfterWrapper0 =
        actionSuccessTlv ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                         : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterWrapper0 = resultAftertlv;
    }
    if (resultAfterWrapper0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      resultAfterWrapper = resultAfterWrapper0;
    }
    else
    {
      ErrorHandlerFn("_WRAPPER",
        "tlv",
        EverParsePulseInternalErrorReasonOfResult(resultAfterWrapper0),
        resultAfterWrapper0 == 0U || (resultAfterWrapper0 >= 2U && resultAfterWrapper0 <= 8U) ? (uint64_t)(uint32_t)resultAfterWrapper0
                                                                                              : 15ULL,
        Ctxt,
        SlBase,
        startPositionWrapper1);
      resultAfterWrapper = resultAfterWrapper0;
    }
  }
  else
  {
    resultAfterWrapper = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
  }
  if (resultAfterWrapper == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterWrapper;
  }
  ErrorHandlerFn("_WRAPPER",
    "__precondition",
    EverParsePulseInternalErrorReasonOfResult(resultAfterWrapper),
    resultAfterWrapper == 0U || (resultAfterWrapper >= 2U && resultAfterWrapper <= 8U) ? (uint64_t)(uint32_t)resultAfterWrapper
                                                                                       : 15ULL,
    Ctxt,
    SlBase,
    startPositionWrapper);
  return resultAfterWrapper;
}

static inline uint8_t
ValidateCoreSpecializedWrapper32(
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartSpecializedWrapper32 = (uint64_t)p1;
  uint64_t startPositionSpecializedWrapper32 = fieldStartSpecializedWrapper32;
  /* Validating field __precondition */
  BOOLEAN preconditionConstraintIsOk = Len > (uint16_t)5U;
  uint8_t resultAfterSpecializedWrapper32;
  size_t p2;
  uint64_t fieldStartSpecializedWrapper321;
  uint64_t startPositionSpecializedWrapper321;
  size_t p3;
  uint64_t fieldStarttlv;
  size_t pos;
  size_t p00;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftertlv;
  uint8_t resultAfterSpecializedWrapper320;
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
  uint32_t res0;
  uint32_t tlv;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionSuccessTlv;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (preconditionConstraintIsOk)
  {
    p2 = *SlPos;
    fieldStartSpecializedWrapper321 = (uint64_t)p2;
    startPositionSpecializedWrapper321 = fieldStartSpecializedWrapper321;
    p3 = *SlPos;
    fieldStarttlv = (uint64_t)p3;
    pos = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p00 = pos;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p00 <= rem && (size_t)4U <= (rem - p00);
    if (hasBytes)
    {
      pos = p00 + (size_t)4U;
      resultAftertlv = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftertlv = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftertlv == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
      res0 = bfirst + n * 256U;
      *SlPos = m;
      tlv = res0;
      src64 = UlongToPtr(tlv);
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit("___specialized_WRAPPER_32.tlv", (uint64_t)(uint32_t)Len, Output);
      if (ok)
      {
        Specialized32ProbeTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
          "___specialized_WRAPPER_32",
          "tlv",
          "probe",
          Ctxt,
          ErrorHandlerFn,
          &readOffset,
          &writeOffset,
          &failed,
          src64,
          Output);
      }
      else
      {
        failed = TRUE;
      }
      wr = writeOffset;
      hasFailed = failed;
      if (hasFailed)
      {
        ErrorHandlerFn("___specialized_WRAPPER_32",
          "tlv",
          "probe",
          0ULL,
          Ctxt,
          EverParseStreamOf(Output),
          0ULL);
        b = 0ULL;
      }
      else
      {
        b = wr;
      }
      if (b != 0ULL)
      {
        base = EverParseStreamOf(Output);
        len = (size_t)EverParseStreamLen(Output);
        cursor = (size_t)0U;
        res =
          ValidateCoreTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
            Ctxt,
            ErrorHandlerFn,
            base,
            len,
            &cursor);
        actionSuccessTlv = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("___specialized_WRAPPER_32",
          "tlv",
          EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
            (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                         : 15ULL,
          Ctxt,
          SlBase,
          fieldStarttlv);
        actionSuccessTlv = FALSE;
      }
      resultAfterSpecializedWrapper320 =
        actionSuccessTlv ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                         : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterSpecializedWrapper320 = resultAftertlv;
    }
    if (resultAfterSpecializedWrapper320 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      resultAfterSpecializedWrapper32 = resultAfterSpecializedWrapper320;
    }
    else
    {
      ErrorHandlerFn("___specialized_WRAPPER_32",
        "tlv",
        EverParsePulseInternalErrorReasonOfResult(resultAfterSpecializedWrapper320),
        resultAfterSpecializedWrapper320 == 0U ||
          (resultAfterSpecializedWrapper320 >= 2U && resultAfterSpecializedWrapper320 <= 8U) ? (uint64_t)(uint32_t)resultAfterSpecializedWrapper320
                                                                                             : 15ULL,
        Ctxt,
        SlBase,
        startPositionSpecializedWrapper321);
      resultAfterSpecializedWrapper32 = resultAfterSpecializedWrapper320;
    }
  }
  else
  {
    resultAfterSpecializedWrapper32 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
  }
  if (resultAfterSpecializedWrapper32 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterSpecializedWrapper32;
  }
  ErrorHandlerFn("___specialized_WRAPPER_32",
    "__precondition",
    EverParsePulseInternalErrorReasonOfResult(resultAfterSpecializedWrapper32),
    resultAfterSpecializedWrapper32 == 0U ||
      (resultAfterSpecializedWrapper32 >= 2U && resultAfterSpecializedWrapper32 <= 8U) ? (uint64_t)(uint32_t)resultAfterSpecializedWrapper32
                                                                                       : 15ULL,
    Ctxt,
    SlBase,
    startPositionSpecializedWrapper32);
  return resultAfterSpecializedWrapper32;
}

static void
EntryProbeWrapper0Tlv(
  uint16_t Arg0,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Err,
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  uint64_t res1;
  BOOLEAN hasFailed;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Fd);
  res1 = Sz;
  hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  rd = *ReadOffset;
  wr = *WriteOffset;
  ok = ProbeAndCopy(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

static uint8_t
ValidateCoreEntry(
  BOOLEAN Requestor32,
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p0;
  uint64_t fieldStartEntry;
  uint64_t startPositionEntry;
  uint8_t resultAfterEntry;
  size_t p1;
  uint64_t fieldStartEntry0;
  uint64_t startPositionEntry0;
  uint8_t resultAfterEntry0;
  size_t pos;
  size_t p2;
  uint64_t viewStart;
  size_t fieldOff;
  uint64_t startPos;
  uint8_t res0;
  uint8_t res;
  size_t consumed;
  size_t p;
  size_t p_;
  if (Requestor32)
  {
    /* Validating field w32 */
    p0 = *SlPos;
    fieldStartEntry = (uint64_t)p0;
    startPositionEntry = fieldStartEntry;
    resultAfterEntry =
      ValidateCoreSpecializedWrapper32(Len,
        Output,
        Ctxt,
        ErrorHandlerFn,
        SlBase,
        SlLen,
        SlPos);
    if (resultAfterEntry == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterEntry;
    }
    ErrorHandlerFn("_ENTRY",
      "w32",
      EverParsePulseInternalErrorReasonOfResult(resultAfterEntry),
      resultAfterEntry == 0U || (resultAfterEntry >= 2U && resultAfterEntry <= 8U) ? (uint64_t)(uint32_t)resultAfterEntry
                                                                                   : 15ULL,
      Ctxt,
      SlBase,
      startPositionEntry);
    return resultAfterEntry;
  }
  if (Requestor32 == FALSE)
  {
    /* Validating field w64 */
    p1 = *SlPos;
    fieldStartEntry0 = (uint64_t)p1;
    startPositionEntry0 = fieldStartEntry0;
    resultAfterEntry0 =
      ValidateCoreWrapper(EntryProbeWrapper0Tlv,
        Len,
        Output,
        Ctxt,
        ErrorHandlerFn,
        SlBase,
        SlLen,
        SlPos);
    if (resultAfterEntry0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterEntry0;
    }
    ErrorHandlerFn("_ENTRY",
      "w64",
      EverParsePulseInternalErrorReasonOfResult(resultAfterEntry0),
      resultAfterEntry0 == 0U || (resultAfterEntry0 >= 2U && resultAfterEntry0 <= 8U) ? (uint64_t)(uint32_t)resultAfterEntry0
                                                                                      : 15ULL,
      Ctxt,
      SlBase,
      startPositionEntry0);
    return resultAfterEntry0;
  }
  pos = (size_t)0U;
  p2 = *SlPos;
  viewStart = (uint64_t)p2;
  fieldOff = pos;
  startPos = viewStart + (uint64_t)fieldOff;
  res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_IMPOSSIBLE;
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res = res0;
  }
  else
  {
    ErrorHandlerFn("_ENTRY",
      "_x_14",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    res = res0;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
    return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  return res;
}

uint64_t
SpecializeDep1ValidateEntry(
  BOOLEAN Requestor32,
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
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
  uint8_t
  status = ValidateCoreEntry(Requestor32, Len, Output, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

