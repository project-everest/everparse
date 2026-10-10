

#include "SpecializeDep1.h"

#include "SpecializeDep1_ExternalAPI.h"

void
SpecializeDep1CopyBytes(
  uint64_t Numbytes,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Tn);
  KRML_MAYBE_UNUSED_VAR(Fn);
  KRML_MAYBE_UNUSED_VAR(Fd);
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(Err);
  KRML_MAYBE_UNUSED_VAR(Sz);
  rd = ReadOffset[0U];
  wr = WriteOffset[0U];
  ok = ProbeAndCopy(Numbytes, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Numbytes;
    WriteOffset[0U] = wr + Numbytes;
    return;
  }
  Failed[0U] = TRUE;
}

void
SpecializeDep1Specialized32ProbeUnion(
  uint8_t Tag,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  BOOLEAN hasFailed0;
  BOOLEAN hasFailed1;
  BOOLEAN hasFailed2;
  if (Tag == 0U)
  {
    SpecializeDep1CopyBytes(1ULL,
      Tn,
      Fn,
      Fd,
      Ctxt,
      Err,
      ReadOffset,
      WriteOffset,
      Failed,
      Src,
      Sz,
      Dest);
    hasFailed = Failed[0U];
    if (hasFailed)
    {
      Err(Tn, Fn, "case0", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  else if (Tag == 1U)
  {
    SpecializeDep1CopyBytes(2ULL,
      Tn,
      Fn,
      Fd,
      Ctxt,
      Err,
      ReadOffset,
      WriteOffset,
      Failed,
      Src,
      Sz,
      Dest);
    hasFailed0 = Failed[0U];
    if (hasFailed0)
    {
      Err(Tn, Fn, "case1", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  else
  {
    SpecializeDep1CopyBytes(4ULL,
      Tn,
      Fn,
      Fd,
      Ctxt,
      Err,
      ReadOffset,
      WriteOffset,
      Failed,
      Src,
      Sz,
      Dest);
    hasFailed1 = Failed[0U];
    if (hasFailed1)
    {
      Err(Tn, Fn, "other", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  hasFailed2 = Failed[0U];
  if (hasFailed2)
  {
    Err(Tn, Fn, "field", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

void
SpecializeDep1Specialized32ProbeTlv(
  uint16_t Len,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  uint64_t rd = ReadOffset[0U];
  uint8_t v = ProbeAndReadU8(Failed, rd, Src, Dest);
  BOOLEAN hasFailed = Failed[0U];
  uint8_t res1;
  BOOLEAN hasFailed1;
  uint64_t wr;
  BOOLEAN ok;
  BOOLEAN hasFailed2;
  BOOLEAN hasFailed3;
  uint64_t ctr;
  BOOLEAN stop;
  BOOLEAN anf0;
  BOOLEAN cond;
  uint64_t c0;
  BOOLEAN hf0;
  uint64_t r0;
  BOOLEAN hasFailed4;
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
    ReadOffset[0U] = rd + 1ULL;
    res1 = v;
  }
  hasFailed1 = Failed[0U];
  if (hasFailed1)
  {
    Err(Tn, Fn, "tag", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  wr = WriteOffset[0U];
  ok = WriteU8(res1, wr, Dest);
  if (ok)
  {
    WriteOffset[0U] = wr + 1ULL;
  }
  else
  {
    Failed[0U] = TRUE;
  }
  hasFailed2 = Failed[0U];
  if (hasFailed2)
  {
    Err(Tn, Fn, "tag", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  SpecializeDep1CopyBytes(4ULL,
    Tn,
    Fn,
    Fd,
    Ctxt,
    Err,
    ReadOffset,
    WriteOffset,
    Failed,
    Src,
    Sz,
    Dest);
  hasFailed3 = Failed[0U];
  if (hasFailed3)
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
    hf0 = Failed[0U];
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
      r0 = ReadOffset[0U];
      SpecializeDep1Specialized32ProbeUnion(res1,
        Tn,
        Fn,
        Fd,
        Ctxt,
        Err,
        ReadOffset,
        WriteOffset,
        Failed,
        Src,
        Sz,
        Dest);
      hasFailed4 = Failed[0U];
      if (hasFailed4)
      {
        Err(Tn, Fn, "payload", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      }
      hf1 = Failed[0U];
      r1 = ReadOffset[0U];
      if (hf1)
      {
        Err(Tn, Fn, Fd, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
        stop = TRUE;
      }
      else if (r1 == r0)
      {
        Err(Tn, Fn, Fd, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
        Failed[0U] = TRUE;
        stop = TRUE;
      }
      else
      {
        bytesRead = r1 - r0;
        if (c0 < bytesRead)
        {
          Err(Tn, Fn, Fd, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
          Failed[0U] = TRUE;
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

inline uint8_t
SpecializeDep1ValidateCoreUnion(
  uint8_t Tag,
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
  size_t pos;
  size_t p;
  uint64_t viewStart1;
  size_t fieldOff1;
  uint64_t startPos1;
  size_t p0;
  size_t p1;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res;
  uint8_t res1;
  size_t consumed;
  size_t p2;
  size_t p_1;
  if (Tag == 0U)
  {
    pos0 = (size_t)0U;
    /* Validating field case0 */
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
      ErrorHandlerFn("_UNION",
        "case0",
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
  if (Tag == 1U)
  {
    pos1 = (size_t)0U;
    /* Validating field case1 */
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
      ErrorHandlerFn("_UNION",
        "case1",
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
  pos = (size_t)0U;
  /* Validating field other */
  p = SlPos[0U];
  viewStart1 = (uint64_t)p;
  fieldOff1 = pos;
  startPos1 = viewStart1 + (uint64_t)fieldOff1;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  p0 = pos;
  p1 = SlPos[0U];
  rem = SlLen - p1;
  hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
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
    res1 = res;
  }
  else
  {
    ErrorHandlerFn("_UNION",
      "other",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos1);
    res1 = res;
  }
  if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_1 = p2 + consumed;
    SlPos[0U] = p_1;
    return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  return res1;
}

inline uint8_t
SpecializeDep1ValidateCoreTlv(
  uint16_t Len,
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
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)1U <= (rem - p0);
  uint8_t res;
  uint8_t resultAftertag;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t tag;
  size_t p2;
  uint64_t fieldStartTlv;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterlength;
  uint8_t resultAfterTlv;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
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
  uint32_t length;
  BOOLEAN lengthConstraintIsOk;
  size_t p4;
  uint64_t fieldStartTlv1;
  size_t nSz;
  size_t p5;
  size_t avail;
  BOOLEAN hasBytes2;
  uint8_t resultAfterTlv0;
  size_t p6;
  size_t tr;
  uint8_t res1;
  BOOLEAN stop;
  BOOLEAN anf0;
  BOOLEAN cond;
  size_t p7;
  size_t avail1;
  BOOLEAN hasMore;
  size_t p8;
  uint64_t fieldStartTlv2;
  uint8_t resultAfterTlv1;
  uint8_t r;
  BOOLEAN anf00;
  uint8_t fres;
  if (hasBytes)
  {
    pos = p0 + (size_t)1U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAftertag = res;
  }
  else
  {
    ErrorHandlerFn("_TLV",
      "tag",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAftertag = res;
  }
  if (resultAftertag == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)1U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    tag = sub[0U];
    p2 = SlPos[0U];
    fieldStartTlv = (uint64_t)p2;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
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
      p03 = SlPos[0U];
      m1 = p03 + (size_t)4U;
      sub1 = SlBase + p03;
      SlPos[0U] = m1;
      first = sub1[0U];
      pos_ = (size_t)2U;
      first1 = sub1[1U];
      pos_1 = pos_ + (size_t)1U;
      first2 = sub1[pos_];
      first3 = sub1[pos_1];
      n = (uint32_t)first3;
      bfirst = (uint32_t)first2;
      n1 = bfirst + n * 256U;
      bfirst1 = (uint32_t)first1;
      n2 = bfirst1 + n1 * 256U;
      bfirst2 = (uint32_t)first;
      length = bfirst2 + n2 * 256U;
      lengthConstraintIsOk = length == (uint32_t)Len;
      if (lengthConstraintIsOk)
      {
        /* Validating field payload */
        p4 = SlPos[0U];
        fieldStartTlv1 = (uint64_t)p4;
        nSz = (size_t)(uint32_t)Len;
        p5 = SlPos[0U];
        avail = SlLen - p5;
        hasBytes2 = nSz <= avail;
        if (!hasBytes2)
        {
          resultAfterTlv0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        else
        {
          p6 = SlPos[0U];
          tr = p6 + nSz;
          res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          stop = FALSE;
          anf0 = stop;
          cond = !anf0;
          while (cond)
          {
            p7 = SlPos[0U];
            avail1 = tr - p7;
            hasMore = (size_t)1U <= avail1;
            if (!hasMore)
            {
              stop = TRUE;
            }
            else
            {
              p8 = SlPos[0U];
              fieldStartTlv2 = (uint64_t)p8;
              resultAfterTlv1 =
                SpecializeDep1ValidateCoreUnion(tag,
                  Ctxt,
                  ErrorHandlerFn,
                  SlBase,
                  tr,
                  SlPos);
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
                  SlBase,
                  fieldStartTlv2);
                r = resultAfterTlv1;
              }
              if (!(r == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS))
              {
                res1 = r;
                stop = TRUE;
              }
            }
            anf00 = stop;
            cond = !anf00;
          }
          fres = res1;
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
            fieldStartTlv1);
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
      fieldStartTlv);
    return resultAfterTlv;
  }
  return resultAftertag;
}

inline uint8_t
SpecializeDep1ValidateCoreSpecializedWrapper32(
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
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
  size_t p = SlPos[0U];
  uint64_t fieldStartSpecializedWrapper32 = (uint64_t)p;
  /* Validating field __precondition */
  BOOLEAN preconditionConstraintIsOk = Len > (uint16_t)5U;
  uint8_t resultAfterSpecializedWrapper32;
  size_t p1;
  uint64_t fieldStartSpecializedWrapper321;
  size_t p2;
  uint64_t fieldStarttlv;
  size_t pos;
  size_t p0;
  size_t p3;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftertlv;
  uint8_t resultAfterSpecializedWrapper320;
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
    p1 = SlPos[0U];
    fieldStartSpecializedWrapper321 = (uint64_t)p1;
    p2 = SlPos[0U];
    fieldStarttlv = (uint64_t)p2;
    pos = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p0 = pos;
    p3 = SlPos[0U];
    rem = SlLen - p3;
    hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
    if (hasBytes)
    {
      pos = p0 + (size_t)4U;
      resultAftertlv = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftertlv = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftertlv == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
      tlv = bfirst2 + n2 * 256U;
      src64 = UlongToPtr(tlv);
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit("___specialized_WRAPPER_32.tlv", (uint64_t)(uint32_t)Len, Output);
      if (ok)
      {
        SpecializeDep1Specialized32ProbeTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
          "___specialized_WRAPPER_32",
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
          SpecializeDep1ValidateCoreTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
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
        fieldStartSpecializedWrapper321);
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
    fieldStartSpecializedWrapper32);
  return resultAfterSpecializedWrapper32;
}

inline uint8_t
SpecializeDep1ValidateCoreWrapper(
  void
  (*ProbeTlv)(
    uint16_t x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    PRIMS_STRING x3,
    uint8_t *x4,
    void
    (*x5)(
      PRIMS_STRING x0,
      PRIMS_STRING x1,
      PRIMS_STRING x2,
      uint64_t x3,
      uint8_t *x4,
      uint8_t *x5,
      uint64_t x6
    ),
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
  size_t p = SlPos[0U];
  uint64_t fieldStartWrapper = (uint64_t)p;
  /* Validating field __precondition */
  BOOLEAN preconditionConstraintIsOk = Len > (uint16_t)5U;
  uint8_t resultAfterWrapper;
  size_t p1;
  uint64_t fieldStartWrapper1;
  size_t p2;
  uint64_t fieldStarttlv;
  size_t pos;
  size_t p0;
  size_t p3;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftertlv;
  uint8_t resultAfterWrapper0;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  size_t pos_;
  uint8_t first1;
  size_t pos_1;
  uint8_t first2;
  size_t pos_2;
  uint8_t first3;
  size_t pos_3;
  uint8_t first4;
  size_t pos_4;
  uint8_t first5;
  size_t pos_5;
  uint8_t first6;
  uint8_t first7;
  uint64_t n;
  uint64_t bfirst;
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
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t tlv;
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
    p1 = SlPos[0U];
    fieldStartWrapper1 = (uint64_t)p1;
    p2 = SlPos[0U];
    fieldStarttlv = (uint64_t)p2;
    pos = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p0 = pos;
    p3 = SlPos[0U];
    rem = SlLen - p3;
    hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
    if (hasBytes)
    {
      pos = p0 + (size_t)8U;
      resultAftertlv = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftertlv = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftertlv == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p01 = SlPos[0U];
      m = p01 + (size_t)8U;
      sub = SlBase + p01;
      SlPos[0U] = m;
      first = sub[0U];
      pos_ = (size_t)2U;
      first1 = sub[1U];
      pos_1 = pos_ + (size_t)1U;
      first2 = sub[pos_];
      pos_2 = pos_1 + (size_t)1U;
      first3 = sub[pos_1];
      pos_3 = pos_2 + (size_t)1U;
      first4 = sub[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first5 = sub[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first6 = sub[pos_4];
      first7 = sub[pos_5];
      n = (uint64_t)(uint32_t)first7;
      bfirst = (uint64_t)(uint32_t)first6;
      n1 = bfirst + n * 256ULL;
      bfirst1 = (uint64_t)(uint32_t)first5;
      n2 = bfirst1 + n1 * 256ULL;
      bfirst2 = (uint64_t)(uint32_t)first4;
      n3 = bfirst2 + n2 * 256ULL;
      bfirst3 = (uint64_t)(uint32_t)first3;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first2;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first1;
      n6 = bfirst5 + n5 * 256ULL;
      bfirst6 = (uint64_t)(uint32_t)first;
      tlv = bfirst6 + n6 * 256ULL;
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
          tlv,
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
          SpecializeDep1ValidateCoreTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
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
        fieldStartWrapper1);
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
    fieldStartWrapper);
  return resultAfterWrapper;
}

void
SpecializeDep1EntryProbeWrapper0Tlv(
  uint16_t Arg0,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Fd);
  hasFailed = Failed[0U];
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  rd = ReadOffset[0U];
  wr = WriteOffset[0U];
  ok = ProbeAndCopy(Sz, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Sz;
    WriteOffset[0U] = wr + Sz;
    return;
  }
  Failed[0U] = TRUE;
}

uint8_t
SpecializeDep1ValidateCoreEntry(
  BOOLEAN Requestor32,
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
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
  size_t p0;
  uint64_t fieldStartEntry;
  uint8_t resultAfterEntry;
  size_t p2;
  uint64_t fieldStartEntry0;
  uint8_t resultAfterEntry0;
  size_t pos;
  size_t p;
  uint64_t viewStart;
  size_t fieldOff;
  uint64_t startPos;
  uint8_t res;
  uint8_t res1;
  size_t consumed;
  size_t p1;
  size_t p_;
  if (Requestor32)
  {
    /* Validating field w32 */
    p0 = SlPos[0U];
    fieldStartEntry = (uint64_t)p0;
    resultAfterEntry =
      SpecializeDep1ValidateCoreSpecializedWrapper32(Len,
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
      fieldStartEntry);
    return resultAfterEntry;
  }
  if (Requestor32 == FALSE)
  {
    /* Validating field w64 */
    p2 = SlPos[0U];
    fieldStartEntry0 = (uint64_t)p2;
    resultAfterEntry0 =
      SpecializeDep1ValidateCoreWrapper(SpecializeDep1EntryProbeWrapper0Tlv,
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
      fieldStartEntry0);
    return resultAfterEntry0;
  }
  pos = (size_t)0U;
  p = SlPos[0U];
  viewStart = (uint64_t)p;
  fieldOff = pos;
  startPos = viewStart + (uint64_t)fieldOff;
  res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_IMPOSSIBLE;
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res1 = res;
  }
  else
  {
    ErrorHandlerFn("_ENTRY",
      "_x_14",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    res1 = res;
  }
  if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p1 = SlPos[0U];
    p_ = p1 + consumed;
    SlPos[0U] = p_;
    return EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  return res1;
}

uint64_t
SpecializeDep1ValidateEntry(
  BOOLEAN Requestor32,
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
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
  uint8_t
  status =
    SpecializeDep1ValidateCoreEntry(Requestor32,
      Len,
      Output,
      Ctxt,
      Handler,
      Input,
      len,
      &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

