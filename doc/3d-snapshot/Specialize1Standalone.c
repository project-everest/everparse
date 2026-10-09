

#include "Specialize1Standalone.h"

#include "Specialize1Standalone_ExternalAPI.h"

static inline uint8_t
ValidateCoreT(
  uint32_t Bound,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos0 = (size_t)0U;
  /* Validating field t1 */
  size_t p1 = *SlPos;
  uint64_t viewStart = (uint64_t)p1;
  size_t fieldOff = pos0;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos0;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t res0;
  uint8_t res1;
  uint8_t resultAftert1;
  size_t consumed;
  size_t p3;
  size_t p_;
  size_t p4;
  uint64_t fieldStartT;
  uint64_t startPositionT;
  size_t pos;
  size_t p01;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftert2_refinement;
  uint8_t resultAfterT;
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
  uint32_t t2_refinement;
  BOOLEAN t2_refinementConstraintIsOk;
  if (hasBytes0)
  {
    pos0 = p00 + (size_t)4U;
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
    ErrorHandlerFn("_T",
      "t1",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    res1 = res0;
  }
  if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos0;
    p3 = *SlPos;
    p_ = p3 + consumed;
    *SlPos = p_;
    resultAftert1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftert1 = res1;
  }
  if (resultAftert1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    /* Validating field t2 */
    p4 = *SlPos;
    fieldStartT = (uint64_t)p4;
    startPositionT = fieldStartT;
    pos = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p01 = pos;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p01 <= rem && (size_t)4U <= (rem - p01);
    if (hasBytes)
    {
      pos = p01 + (size_t)4U;
      resultAftert2_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftert2_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftert2_refinement == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      /* reading field_value */
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
      t2_refinement = res;
      /* start: checking constraint */
      t2_refinementConstraintIsOk = t2_refinement <= Bound;
      /* end: checking constraint */
      resultAfterT =
        t2_refinementConstraintIsOk ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                                    : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
    else
    {
      resultAfterT = resultAftert2_refinement;
    }
    if (resultAfterT == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterT;
    }
    ErrorHandlerFn("_T",
      "t2.refinement",
      EverParsePulseInternalErrorReasonOfResult(resultAfterT),
      resultAfterT == 0U || (resultAfterT >= 2U && resultAfterT <= 8U) ? (uint64_t)(uint32_t)resultAfterT
                                                                       : 15ULL,
      Ctxt,
      SlBase,
      startPositionT);
    return resultAfterT;
  }
  return resultAftert1;
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
  BOOLEAN ok = ProbeAndCopy0(Numbytes, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + Numbytes;
    *WriteOffset = wr + Numbytes;
    return;
  }
  *Failed = TRUE;
}

static void SkipBytesWrite(uint64_t Numbytes, uint64_t *WriteOffset, BOOLEAN *Failed)
{
  uint64_t wr = *WriteOffset;
  if (wr <= (0xffffffffffffffffULL - Numbytes))
  {
    *WriteOffset = wr + Numbytes;
    return;
  }
  *Failed = TRUE;
}

static void
ReadAndCoercePointer(
  PRIMS_STRING Fieldname,
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
  uint32_t v = ProbeAndReadU320(Failed, rd, Src, Dest);
  BOOLEAN hasFailed = *Failed;
  uint32_t res1;
  BOOLEAN hasFailed0;
  uint64_t res11;
  BOOLEAN hasFailed1;
  uint64_t wr;
  BOOLEAN ok;
  if (hasFailed)
  {
    Err(Tn, Fn, Fd, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    res1 = v;
  }
  else
  {
    *ReadOffset = rd + 4ULL;
    res1 = v;
  }
  hasFailed0 = *Failed;
  if (hasFailed0)
  {
    Err(Tn, Fn, Fieldname, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  res11 = UlongToPtr0(res1);
  hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, Fieldname, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  wr = *WriteOffset;
  ok = WriteU640(res11, wr, Dest);
  if (ok)
  {
    *WriteOffset = wr + 8ULL;
    return;
  }
  *Failed = TRUE;
}

static void
Specialized32ProbeT(
  uint32_t Bound,
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
  BOOLEAN hasFailed;
  KRML_MAYBE_UNUSED_VAR(Bound);
  KRML_MAYBE_UNUSED_VAR(Fd);
  KRML_MAYBE_UNUSED_VAR(Sz);
  CopyBytes(8ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "t1", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint8_t
ValidateCoreS64(
  void
  (*ProbePtrT)(
    uint32_t x0,
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
  uint32_t Bound,
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartS64 = (uint64_t)p1;
  uint64_t startPositionS64 = fieldStartS64;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t resultAfters1;
  uint8_t resultAfterS64;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t first0;
  size_t pos_1;
  uint8_t first10;
  size_t pos_2;
  uint8_t first20;
  uint8_t first30;
  uint32_t n0;
  uint32_t bfirst0;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t res0;
  uint32_t s1;
  BOOLEAN s1ConstraintIsOk;
  size_t p3;
  uint64_t fieldStartS641;
  uint64_t startPositionS641;
  size_t pos10;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res1;
  uint8_t resultAfterS640;
  size_t consumed0;
  size_t p5;
  size_t p_;
  uint8_t resultAfterAlignmentPadding7;
  size_t p6;
  uint64_t fieldStartS6410;
  uint64_t startPositionS6410;
  size_t p7;
  uint64_t fieldStartptrT;
  size_t pos11;
  size_t p03;
  size_t p8;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t resultAfterptrT0;
  uint8_t resultAfterS641;
  size_t p04;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t first;
  size_t pos_10;
  uint8_t first1;
  size_t pos_20;
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
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t n7;
  uint64_t bfirst7;
  uint64_t n8;
  uint64_t bfirst8;
  uint64_t n;
  uint64_t bfirst;
  uint64_t res2;
  uint64_t ptrT;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionSuccessPtrT;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res3;
  uint8_t resultAfterptrT;
  size_t p9;
  uint64_t fieldStartS6411;
  uint64_t startPositionS6411;
  size_t pos1;
  size_t p0;
  size_t p10;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res;
  uint8_t resultAfterS642;
  size_t consumed;
  size_t p;
  size_t p_0;
  if (hasBytes0)
  {
    pos = p00 + (size_t)4U;
    resultAfters1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfters1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfters1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)4U;
    sub0 = SlBase + p01;
    pos_ = (size_t)1U;
    first0 = sub0[0U];
    pos_1 = pos_ + (size_t)1U;
    first10 = sub0[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first20 = sub0[pos_1];
    first30 = sub0[pos_2];
    n0 = (uint32_t)first30;
    bfirst0 = (uint32_t)first20;
    n1 = bfirst0 + n0 * 256U;
    bfirst1 = (uint32_t)first10;
    n2 = bfirst1 + n1 * 256U;
    bfirst2 = (uint32_t)first0;
    res0 = bfirst2 + n2 * 256U;
    *SlPos = m0;
    s1 = res0;
    s1ConstraintIsOk = s1 <= Bound;
    if (s1ConstraintIsOk)
    {
      /* Validating field ___alignment_padding_7 */
      p3 = *SlPos;
      fieldStartS641 = (uint64_t)p3;
      startPositionS641 = fieldStartS641;
      pos10 = (size_t)0U;
      p02 = pos10;
      p4 = *SlPos;
      rem1 = SlLen - p4;
      hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
      if (hasBytes1)
      {
        pos10 = p02 + (size_t)4U;
        res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        consumed0 = pos10;
        p5 = *SlPos;
        p_ = p5 + consumed0;
        *SlPos = p_;
        resultAfterS640 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterS640 = res1;
      }
      if (resultAfterS640 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        resultAfterAlignmentPadding7 = resultAfterS640;
      }
      else
      {
        ErrorHandlerFn("_S64",
          "___alignment_padding_7",
          EverParsePulseInternalErrorReasonOfResult(resultAfterS640),
          resultAfterS640 == 0U || (resultAfterS640 >= 2U && resultAfterS640 <= 8U) ? (uint64_t)(uint32_t)resultAfterS640
                                                                                    : 15ULL,
          Ctxt,
          SlBase,
          startPositionS641);
        resultAfterAlignmentPadding7 = resultAfterS640;
      }
      if (resultAfterAlignmentPadding7 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        p6 = *SlPos;
        fieldStartS6410 = (uint64_t)p6;
        startPositionS6410 = fieldStartS6410;
        p7 = *SlPos;
        fieldStartptrT = (uint64_t)p7;
        pos11 = (size_t)0U;
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        p03 = pos11;
        p8 = *SlPos;
        rem2 = SlLen - p8;
        hasBytes2 = p03 <= rem2 && (size_t)8U <= (rem2 - p03);
        if (hasBytes2)
        {
          pos11 = p03 + (size_t)8U;
          resultAfterptrT0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAfterptrT0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (resultAfterptrT0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          p04 = *SlPos;
          m = p04 + (size_t)8U;
          sub = SlBase + p04;
          pos_0 = (size_t)1U;
          first = sub[0U];
          pos_10 = pos_0 + (size_t)1U;
          first1 = sub[pos_0];
          pos_20 = pos_10 + (size_t)1U;
          first2 = sub[pos_10];
          pos_3 = pos_20 + (size_t)1U;
          first3 = sub[pos_20];
          pos_4 = pos_3 + (size_t)1U;
          first4 = sub[pos_3];
          pos_5 = pos_4 + (size_t)1U;
          first5 = sub[pos_4];
          pos_6 = pos_5 + (size_t)1U;
          first6 = sub[pos_5];
          first7 = sub[pos_6];
          n3 = (uint64_t)(uint32_t)first7;
          bfirst3 = (uint64_t)(uint32_t)first6;
          n4 = bfirst3 + n3 * 256ULL;
          bfirst4 = (uint64_t)(uint32_t)first5;
          n5 = bfirst4 + n4 * 256ULL;
          bfirst5 = (uint64_t)(uint32_t)first4;
          n6 = bfirst5 + n5 * 256ULL;
          bfirst6 = (uint64_t)(uint32_t)first3;
          n7 = bfirst6 + n6 * 256ULL;
          bfirst7 = (uint64_t)(uint32_t)first2;
          n8 = bfirst7 + n7 * 256ULL;
          bfirst8 = (uint64_t)(uint32_t)first1;
          n = bfirst8 + n8 * 256ULL;
          bfirst = (uint64_t)(uint32_t)first;
          res2 = bfirst + n * 256ULL;
          *SlPos = m;
          ptrT = res2;
          src64 = ptrT;
          readOffset = 0ULL;
          writeOffset = 0ULL;
          failed = FALSE;
          ok = ProbeInit0("_S64.ptrT", (uint64_t)8U, Dest);
          if (ok)
          {
            ProbePtrT(s1,
              "_S64",
              "ptrT",
              "probe",
              Ctxt,
              ErrorHandlerFn,
              &readOffset,
              &writeOffset,
              &failed,
              src64,
              (uint64_t)8U,
              Dest);
          }
          else
          {
            failed = TRUE;
          }
          wr = writeOffset;
          hasFailed = failed;
          if (hasFailed)
          {
            ErrorHandlerFn("_S64", "ptrT", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
            b = 0ULL;
          }
          else
          {
            b = wr;
          }
          if (b != 0ULL)
          {
            base = EverParseStreamOf(Dest);
            len = (size_t)EverParseStreamLen(Dest);
            cursor = (size_t)0U;
            res3 = ValidateCoreT(s1, Ctxt, ErrorHandlerFn, base, len, &cursor);
            actionSuccessPtrT = res3 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          }
          else
          {
            ErrorHandlerFn("_S64",
              "ptrT",
              EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
                (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
                  EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                             : 15ULL,
              Ctxt,
              SlBase,
              fieldStartptrT);
            actionSuccessPtrT = FALSE;
          }
          resultAfterS641 =
            actionSuccessPtrT ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                              : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
        }
        else
        {
          resultAfterS641 = resultAfterptrT0;
        }
        if (resultAfterS641 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          resultAfterptrT = resultAfterS641;
        }
        else
        {
          ErrorHandlerFn("_S64",
            "ptrT",
            EverParsePulseInternalErrorReasonOfResult(resultAfterS641),
            resultAfterS641 == 0U || (resultAfterS641 >= 2U && resultAfterS641 <= 8U) ? (uint64_t)(uint32_t)resultAfterS641
                                                                                      : 15ULL,
            Ctxt,
            SlBase,
            startPositionS6410);
          resultAfterptrT = resultAfterS641;
        }
        if (resultAfterptrT == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          p9 = *SlPos;
          fieldStartS6411 = (uint64_t)p9;
          startPositionS6411 = fieldStartS6411;
          pos1 = (size_t)0U;
          p0 = pos1;
          p10 = *SlPos;
          rem = SlLen - p10;
          hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
          if (hasBytes)
          {
            pos1 = p0 + (size_t)8U;
            res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          }
          else
          {
            res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
          }
          if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
          {
            consumed = pos1;
            p = *SlPos;
            p_0 = p + consumed;
            *SlPos = p_0;
            resultAfterS642 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          }
          else
          {
            resultAfterS642 = res;
          }
          if (resultAfterS642 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
          {
            resultAfterS64 = resultAfterS642;
          }
          else
          {
            ErrorHandlerFn("_S64",
              "s2",
              EverParsePulseInternalErrorReasonOfResult(resultAfterS642),
              resultAfterS642 == 0U || (resultAfterS642 >= 2U && resultAfterS642 <= 8U) ? (uint64_t)(uint32_t)resultAfterS642
                                                                                        : 15ULL,
              Ctxt,
              SlBase,
              startPositionS6411);
            resultAfterS64 = resultAfterS642;
          }
        }
        else
        {
          resultAfterS64 = resultAfterptrT;
        }
      }
      else
      {
        resultAfterS64 = resultAfterAlignmentPadding7;
      }
    }
    else
    {
      resultAfterS64 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
  }
  else
  {
    resultAfterS64 = resultAfters1;
  }
  if (resultAfterS64 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterS64;
  }
  ErrorHandlerFn("_S64",
    "s1",
    EverParsePulseInternalErrorReasonOfResult(resultAfterS64),
    resultAfterS64 == 0U || (resultAfterS64 >= 2U && resultAfterS64 <= 8U) ? (uint64_t)(uint32_t)resultAfterS64
                                                                           : 15ULL,
    Ctxt,
    SlBase,
    startPositionS64);
  return resultAfterS64;
}

static void
Specialized32ProbeS64(
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
  BOOLEAN hasFailed;
  BOOLEAN hasFailed1;
  BOOLEAN hasFailed2;
  BOOLEAN hasFailed3;
  BOOLEAN hasFailed4;
  CopyBytes(4ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "s1", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  SkipBytesWrite(4ULL, WriteOffset, Failed);
  hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, "alignment", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  ReadAndCoercePointer("ptrT",
    Tn,
    Fn,
    Fd,
    Ctxt,
    Err,
    ReadOffset,
    WriteOffset,
    Failed,
    Src,
    Dest);
  hasFailed2 = *Failed;
  if (hasFailed2)
  {
    Err(Tn, Fn, "ptrT", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  CopyBytes(4ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  hasFailed3 = *Failed;
  if (hasFailed3)
  {
    Err(Tn, Fn, "s2", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  SkipBytesWrite(4ULL, WriteOffset, Failed);
  hasFailed4 = *Failed;
  if (hasFailed4)
  {
    Err(Tn, Fn, "alignment", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint8_t
ValidateCoreR64(
  void
  (*ProbeS640)(
    uint32_t x0,
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
  void
  (*ProbePtrS)(
    uint32_t x0,
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
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterr1;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t first0;
  size_t pos_1;
  uint8_t first10;
  size_t pos_2;
  uint8_t first20;
  uint8_t first30;
  uint32_t n0;
  uint32_t bfirst0;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t res1;
  uint32_t r1;
  size_t p3;
  uint64_t fieldStartR64;
  uint64_t startPositionR64;
  size_t pos10;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res2;
  uint8_t resultAfterR64;
  size_t consumed;
  size_t p5;
  size_t p_;
  uint8_t resultAfterAlignmentPadding9;
  size_t p6;
  uint64_t fieldStartR640;
  uint64_t startPositionR640;
  size_t p7;
  uint64_t fieldStartptrS;
  size_t pos1;
  size_t p03;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAfterptrS;
  uint8_t resultAfterR640;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t first;
  size_t pos_10;
  uint8_t first1;
  size_t pos_20;
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
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t n7;
  uint64_t bfirst7;
  uint64_t n8;
  uint64_t bfirst8;
  uint64_t n;
  uint64_t bfirst;
  uint64_t res3;
  uint64_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionSuccessPtrS;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (hasBytes0)
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
    resultAfterr1 = res0;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "r1",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterr1 = res0;
  }
  if (resultAfterr1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)4U;
    sub0 = SlBase + p01;
    pos_ = (size_t)1U;
    first0 = sub0[0U];
    pos_1 = pos_ + (size_t)1U;
    first10 = sub0[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first20 = sub0[pos_1];
    first30 = sub0[pos_2];
    n0 = (uint32_t)first30;
    bfirst0 = (uint32_t)first20;
    n1 = bfirst0 + n0 * 256U;
    bfirst1 = (uint32_t)first10;
    n2 = bfirst1 + n1 * 256U;
    bfirst2 = (uint32_t)first0;
    res1 = bfirst2 + n2 * 256U;
    *SlPos = m0;
    r1 = res1;
    /* Validating field ___alignment_padding_9 */
    p3 = *SlPos;
    fieldStartR64 = (uint64_t)p3;
    startPositionR64 = fieldStartR64;
    pos10 = (size_t)0U;
    p02 = pos10;
    p4 = *SlPos;
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos10 = p02 + (size_t)4U;
      res2 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res2 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed = pos10;
      p5 = *SlPos;
      p_ = p5 + consumed;
      *SlPos = p_;
      resultAfterR64 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterR64 = res2;
    }
    if (resultAfterR64 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      resultAfterAlignmentPadding9 = resultAfterR64;
    }
    else
    {
      ErrorHandlerFn("_R64",
        "___alignment_padding_9",
        EverParsePulseInternalErrorReasonOfResult(resultAfterR64),
        resultAfterR64 == 0U || (resultAfterR64 >= 2U && resultAfterR64 <= 8U) ? (uint64_t)(uint32_t)resultAfterR64
                                                                               : 15ULL,
        Ctxt,
        SlBase,
        startPositionR64);
      resultAfterAlignmentPadding9 = resultAfterR64;
    }
    if (resultAfterAlignmentPadding9 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p6 = *SlPos;
      fieldStartR640 = (uint64_t)p6;
      startPositionR640 = fieldStartR640;
      p7 = *SlPos;
      fieldStartptrS = (uint64_t)p7;
      pos1 = (size_t)0U;
      /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
      p03 = pos1;
      p = *SlPos;
      rem = SlLen - p;
      hasBytes = p03 <= rem && (size_t)8U <= (rem - p03);
      if (hasBytes)
      {
        pos1 = p03 + (size_t)8U;
        resultAfterptrS = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterptrS = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (resultAfterptrS == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        p0 = *SlPos;
        m = p0 + (size_t)8U;
        sub = SlBase + p0;
        pos_0 = (size_t)1U;
        first = sub[0U];
        pos_10 = pos_0 + (size_t)1U;
        first1 = sub[pos_0];
        pos_20 = pos_10 + (size_t)1U;
        first2 = sub[pos_10];
        pos_3 = pos_20 + (size_t)1U;
        first3 = sub[pos_20];
        pos_4 = pos_3 + (size_t)1U;
        first4 = sub[pos_3];
        pos_5 = pos_4 + (size_t)1U;
        first5 = sub[pos_4];
        pos_6 = pos_5 + (size_t)1U;
        first6 = sub[pos_5];
        first7 = sub[pos_6];
        n3 = (uint64_t)(uint32_t)first7;
        bfirst3 = (uint64_t)(uint32_t)first6;
        n4 = bfirst3 + n3 * 256ULL;
        bfirst4 = (uint64_t)(uint32_t)first5;
        n5 = bfirst4 + n4 * 256ULL;
        bfirst5 = (uint64_t)(uint32_t)first4;
        n6 = bfirst5 + n5 * 256ULL;
        bfirst6 = (uint64_t)(uint32_t)first3;
        n7 = bfirst6 + n6 * 256ULL;
        bfirst7 = (uint64_t)(uint32_t)first2;
        n8 = bfirst7 + n7 * 256ULL;
        bfirst8 = (uint64_t)(uint32_t)first1;
        n = bfirst8 + n8 * 256ULL;
        bfirst = (uint64_t)(uint32_t)first;
        res3 = bfirst + n * 256ULL;
        *SlPos = m;
        ptrS = res3;
        src64 = ptrS;
        readOffset = 0ULL;
        writeOffset = 0ULL;
        failed = FALSE;
        ok = ProbeInit0("_R64.ptrS", (uint64_t)24U, DestS);
        if (ok)
        {
          ProbePtrS(r1,
            "_R64",
            "ptrS",
            "probe",
            Ctxt,
            ErrorHandlerFn,
            &readOffset,
            &writeOffset,
            &failed,
            src64,
            (uint64_t)24U,
            DestS);
        }
        else
        {
          failed = TRUE;
        }
        wr = writeOffset;
        hasFailed = failed;
        if (hasFailed)
        {
          ErrorHandlerFn("_R64", "ptrS", "probe", 0ULL, Ctxt, EverParseStreamOf(DestS), 0ULL);
          b = 0ULL;
        }
        else
        {
          b = wr;
        }
        if (b != 0ULL)
        {
          base = EverParseStreamOf(DestS);
          len = (size_t)EverParseStreamLen(DestS);
          cursor = (size_t)0U;
          res = ValidateCoreS64(ProbeS640, r1, DestT, Ctxt, ErrorHandlerFn, base, len, &cursor);
          actionSuccessPtrS = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          ErrorHandlerFn("_R64",
            "ptrS",
            EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
            EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
              (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
                EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                           : 15ULL,
            Ctxt,
            SlBase,
            fieldStartptrS);
          actionSuccessPtrS = FALSE;
        }
        resultAfterR640 =
          actionSuccessPtrS ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                            : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
      }
      else
      {
        resultAfterR640 = resultAfterptrS;
      }
      if (resultAfterR640 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        return resultAfterR640;
      }
      ErrorHandlerFn("_R64",
        "ptrS",
        EverParsePulseInternalErrorReasonOfResult(resultAfterR640),
        resultAfterR640 == 0U || (resultAfterR640 >= 2U && resultAfterR640 <= 8U) ? (uint64_t)(uint32_t)resultAfterR640
                                                                                  : 15ULL,
        Ctxt,
        SlBase,
        startPositionR640);
      return resultAfterR640;
    }
    return resultAfterAlignmentPadding9;
  }
  return resultAfterr1;
}

static inline uint8_t
ValidateCoreSpecializedR32(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterr1;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t first0;
  size_t pos_1;
  uint8_t first10;
  size_t pos_2;
  uint8_t first20;
  uint8_t first30;
  uint32_t n0;
  uint32_t bfirst0;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t res1;
  uint32_t r1;
  size_t p3;
  uint64_t fieldStartSpecializedR32;
  uint64_t startPositionSpecializedR32;
  size_t p4;
  uint64_t fieldStartptrS;
  size_t pos1;
  size_t p02;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAfterptrS;
  uint8_t resultAfterSpecializedR32;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t first;
  size_t pos_10;
  uint8_t first1;
  size_t pos_20;
  uint8_t first2;
  uint8_t first3;
  uint32_t n3;
  uint32_t bfirst3;
  uint32_t n4;
  uint32_t bfirst4;
  uint32_t n;
  uint32_t bfirst;
  uint32_t res2;
  uint32_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionSuccessPtrS;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (hasBytes0)
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
    resultAfterr1 = res0;
  }
  else
  {
    ErrorHandlerFn("___specialized_R32",
      "r1",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterr1 = res0;
  }
  if (resultAfterr1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)4U;
    sub0 = SlBase + p01;
    pos_ = (size_t)1U;
    first0 = sub0[0U];
    pos_1 = pos_ + (size_t)1U;
    first10 = sub0[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first20 = sub0[pos_1];
    first30 = sub0[pos_2];
    n0 = (uint32_t)first30;
    bfirst0 = (uint32_t)first20;
    n1 = bfirst0 + n0 * 256U;
    bfirst1 = (uint32_t)first10;
    n2 = bfirst1 + n1 * 256U;
    bfirst2 = (uint32_t)first0;
    res1 = bfirst2 + n2 * 256U;
    *SlPos = m0;
    r1 = res1;
    p3 = *SlPos;
    fieldStartSpecializedR32 = (uint64_t)p3;
    startPositionSpecializedR32 = fieldStartSpecializedR32;
    p4 = *SlPos;
    fieldStartptrS = (uint64_t)p4;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p02 <= rem && (size_t)4U <= (rem - p02);
    if (hasBytes)
    {
      pos1 = p02 + (size_t)4U;
      resultAfterptrS = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterptrS = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterptrS == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p0 = *SlPos;
      m = p0 + (size_t)4U;
      sub = SlBase + p0;
      pos_0 = (size_t)1U;
      first = sub[0U];
      pos_10 = pos_0 + (size_t)1U;
      first1 = sub[pos_0];
      pos_20 = pos_10 + (size_t)1U;
      first2 = sub[pos_10];
      first3 = sub[pos_20];
      n3 = (uint32_t)first3;
      bfirst3 = (uint32_t)first2;
      n4 = bfirst3 + n3 * 256U;
      bfirst4 = (uint32_t)first1;
      n = bfirst4 + n4 * 256U;
      bfirst = (uint32_t)first;
      res2 = bfirst + n * 256U;
      *SlPos = m;
      ptrS = res2;
      src64 = UlongToPtr0(ptrS);
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit0("___specialized_R32.ptrS", (uint64_t)24U, DestS);
      if (ok)
      {
        Specialized32ProbeS64("___specialized_R32",
          "ptrS",
          "probe",
          Ctxt,
          ErrorHandlerFn,
          &readOffset,
          &writeOffset,
          &failed,
          src64,
          DestS);
      }
      else
      {
        failed = TRUE;
      }
      wr = writeOffset;
      hasFailed = failed;
      if (hasFailed)
      {
        ErrorHandlerFn("___specialized_R32",
          "ptrS",
          "probe",
          0ULL,
          Ctxt,
          EverParseStreamOf(DestS),
          0ULL);
        b = 0ULL;
      }
      else
      {
        b = wr;
      }
      if (b != 0ULL)
      {
        base = EverParseStreamOf(DestS);
        len = (size_t)EverParseStreamLen(DestS);
        cursor = (size_t)0U;
        res =
          ValidateCoreS64(Specialized32ProbeT,
            r1,
            DestT,
            Ctxt,
            ErrorHandlerFn,
            base,
            len,
            &cursor);
        actionSuccessPtrS = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("___specialized_R32",
          "ptrS",
          EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
            (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                         : 15ULL,
          Ctxt,
          SlBase,
          fieldStartptrS);
        actionSuccessPtrS = FALSE;
      }
      resultAfterSpecializedR32 =
        actionSuccessPtrS ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                          : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterSpecializedR32 = resultAfterptrS;
    }
    if (resultAfterSpecializedR32 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterSpecializedR32;
    }
    ErrorHandlerFn("___specialized_R32",
      "ptrS",
      EverParsePulseInternalErrorReasonOfResult(resultAfterSpecializedR32),
      resultAfterSpecializedR32 == 0U ||
        (resultAfterSpecializedR32 >= 2U && resultAfterSpecializedR32 <= 8U) ? (uint64_t)(uint32_t)resultAfterSpecializedR32
                                                                             : 15ULL,
      Ctxt,
      SlBase,
      startPositionSpecializedR32);
    return resultAfterSpecializedR32;
  }
  return resultAfterr1;
}

static void
RProbeFieldR640T(
  uint32_t Arg0,
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
  ok = ProbeAndCopy0(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

static void
RProbeFieldR641S64(
  uint32_t Arg0,
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
  ok = ProbeAndCopy0(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

static uint8_t
ValidateCoreR(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p0;
  uint64_t fieldStartR;
  uint64_t startPositionR;
  uint8_t resultAfterR;
  size_t p;
  uint64_t fieldStartR0;
  uint64_t startPositionR0;
  uint8_t resultAfterR0;
  if (Requestor32)
  {
    /* Validating field r32 */
    p0 = *SlPos;
    fieldStartR = (uint64_t)p0;
    startPositionR = fieldStartR;
    resultAfterR =
      ValidateCoreSpecializedR32(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        SlBase,
        SlLen,
        SlPos);
    if (resultAfterR == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterR;
    }
    ErrorHandlerFn("___R",
      "r32",
      EverParsePulseInternalErrorReasonOfResult(resultAfterR),
      resultAfterR == 0U || (resultAfterR >= 2U && resultAfterR <= 8U) ? (uint64_t)(uint32_t)resultAfterR
                                                                       : 15ULL,
      Ctxt,
      SlBase,
      startPositionR);
    return resultAfterR;
  }
  /* Validating field r64 */
  p = *SlPos;
  fieldStartR0 = (uint64_t)p;
  startPositionR0 = fieldStartR0;
  resultAfterR0 =
    ValidateCoreR64(RProbeFieldR640T,
      RProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      SlBase,
      SlLen,
      SlPos);
  if (resultAfterR0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterR0;
  }
  ErrorHandlerFn("___R",
    "r64",
    EverParsePulseInternalErrorReasonOfResult(resultAfterR0),
    resultAfterR0 == 0U || (resultAfterR0 >= 2U && resultAfterR0 <= 8U) ? (uint64_t)(uint32_t)resultAfterR0
                                                                        : 15ULL,
    Ctxt,
    SlBase,
    startPositionR0);
  return resultAfterR0;
}

uint64_t
Specialize1standaloneValidateR(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  uint8_t status = ValidateCoreR(Requestor32, DestS, DestT, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

