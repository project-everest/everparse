

#include "Specialize1.h"

#include "Specialize1_ExternalAPI.h"
#include "EverParse.h"

void
Specialize1CopyBytes(
  uint64_t Numbytes,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  ok = ProbeAndCopy1(Numbytes, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Numbytes;
    WriteOffset[0U] = wr + Numbytes;
    return;
  }
  Failed[0U] = TRUE;
}

void
Specialize1SkipBytesWrite(
  uint64_t Numbytes,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  uint64_t wr;
  KRML_MAYBE_UNUSED_VAR(Tn);
  KRML_MAYBE_UNUSED_VAR(Fn);
  KRML_MAYBE_UNUSED_VAR(Fd);
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(Err);
  KRML_MAYBE_UNUSED_VAR(ReadOffset);
  KRML_MAYBE_UNUSED_VAR(Src);
  KRML_MAYBE_UNUSED_VAR(Sz);
  KRML_MAYBE_UNUSED_VAR(Dest);
  wr = WriteOffset[0U];
  if (wr <= (0xffffffffffffffffULL - Numbytes))
  {
    WriteOffset[0U] = wr + Numbytes;
    return;
  }
  Failed[0U] = TRUE;
}

void
Specialize1ReadAndCoercePointer(
  EVERPARSE_STRING Fieldname,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  uint64_t rd;
  uint32_t v;
  BOOLEAN hasFailed;
  uint32_t res1;
  size_t p0;
  uint64_t position0;
  BOOLEAN hasFailed1;
  size_t p1;
  uint64_t position1;
  uint64_t res11;
  BOOLEAN hasFailed2;
  size_t p;
  uint64_t position;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Sz);
  rd = ReadOffset[0U];
  v = ProbeAndReadU320(Failed, rd, Src, Dest);
  hasFailed = Failed[0U];
  if (hasFailed)
  {
    p0 = EverParseStreamPos(Dest)[0U];
    position0 = (uint64_t)p0;
    Err(Tn,
      Fn,
      Fd,
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position0);
    res1 = v;
  }
  else
  {
    ReadOffset[0U] = rd + 4ULL;
    res1 = v;
  }
  hasFailed1 = Failed[0U];
  if (hasFailed1)
  {
    p1 = EverParseStreamPos(Dest)[0U];
    position1 = (uint64_t)p1;
    Err(Tn,
      Fn,
      Fieldname,
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position1);
    return;
  }
  res11 = UlongToPtr1(res1);
  hasFailed2 = Failed[0U];
  if (hasFailed2)
  {
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      Fieldname,
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
  wr = WriteOffset[0U];
  ok = WriteU640(res11, wr, Dest);
  if (ok)
  {
    WriteOffset[0U] = wr + 8ULL;
    return;
  }
  Failed[0U] = TRUE;
}

void
Specialize1Specialized32ProbeS64(
  uint32_t Bound,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  size_t p0;
  uint64_t position0;
  BOOLEAN hasFailed1;
  size_t p1;
  uint64_t position1;
  BOOLEAN hasFailed2;
  size_t p2;
  uint64_t position2;
  BOOLEAN hasFailed3;
  size_t p3;
  uint64_t position3;
  BOOLEAN hasFailed4;
  size_t p;
  uint64_t position;
  KRML_MAYBE_UNUSED_VAR(Bound);
  Specialize1CopyBytes(4ULL,
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
    p0 = EverParseStreamPos(Dest)[0U];
    position0 = (uint64_t)p0;
    Err(Tn,
      Fn,
      "s1",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position0);
    return;
  }
  Specialize1SkipBytesWrite(4ULL,
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
    p1 = EverParseStreamPos(Dest)[0U];
    position1 = (uint64_t)p1;
    Err(Tn,
      Fn,
      "alignment",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position1);
    return;
  }
  Specialize1ReadAndCoercePointer("ptrT",
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
  hasFailed2 = Failed[0U];
  if (hasFailed2)
  {
    p2 = EverParseStreamPos(Dest)[0U];
    position2 = (uint64_t)p2;
    Err(Tn,
      Fn,
      "ptrT",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position2);
    return;
  }
  Specialize1CopyBytes(4ULL,
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
    p3 = EverParseStreamPos(Dest)[0U];
    position3 = (uint64_t)p3;
    Err(Tn,
      Fn,
      "s2",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position3);
    return;
  }
  Specialize1SkipBytesWrite(4ULL,
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
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      "alignment",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
}

inline uint8_t
Specialize1ValidateT(
  uint32_t Bound,
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
  size_t pos = (size_t)0U;
  /* Validating field t1 */
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
  uint8_t res1;
  uint8_t resultAftert1;
  size_t consumed;
  size_t p20;
  size_t p_;
  size_t p2;
  uint64_t fieldStartT;
  size_t pos1;
  size_t p01;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAftert2_refinement;
  uint8_t resultAfterT;
  size_t p02;
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
  uint32_t t2_refinement;
  BOOLEAN t2_refinementConstraintIsOk;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    res1 = res;
  }
  else
  {
    ErrorHandlerFn("_T",
      "t1",
      EverParseErrorReasonOfResult(res),
      res,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    res1 = res;
  }
  if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p20 = SlPos[0U];
    p_ = p20 + consumed;
    SlPos[0U] = p_;
    resultAftert1 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftert1 = res1;
  }
  if (resultAftert1 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    /* Validating field t2 */
    p2 = SlPos[0U];
    fieldStartT = (uint64_t)p2;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p01 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p01 <= rem1 && (size_t)4U <= (rem1 - p01);
    if (hasBytes1)
    {
      pos1 = p01 + (size_t)4U;
      resultAftert2_refinement = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftert2_refinement = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftert2_refinement == EVERPARSE_VALIDATOR_SUCCESS)
    {
      /* reading field_value */
      p02 = SlPos[0U];
      m = p02 + (size_t)4U;
      sub = SlBase + p02;
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
      t2_refinement = bfirst2 + n2 * 256U;
      /* start: checking constraint */
      t2_refinementConstraintIsOk = t2_refinement <= Bound;
      /* end: checking constraint */
      resultAfterT =
        t2_refinementConstraintIsOk ? EVERPARSE_VALIDATOR_SUCCESS
                                    : EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
    else
    {
      resultAfterT = resultAftert2_refinement;
    }
    if (resultAfterT == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterT;
    }
    ErrorHandlerFn("_T",
      "t2.refinement",
      EverParseErrorReasonOfResult(resultAfterT),
      resultAfterT,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartT);
    return resultAfterT;
  }
  return resultAftert1;
}

inline uint8_t
Specialize1ValidateS64(
  void
  (*ProbePtrT)(
    uint32_t x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    EVERPARSE_STRING x3,
    uint8_t *x4,
    void
    (*x5)(
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
  uint64_t fieldStartS64 = (uint64_t)p;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t resultAfters1;
  uint8_t resultAfterS64;
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
  uint32_t s1;
  BOOLEAN s1ConstraintIsOk;
  size_t p2;
  uint64_t fieldStartS641;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res;
  uint8_t resultAfterS640;
  size_t consumed0;
  size_t p40;
  size_t p_;
  uint8_t resultAfterAlignmentPadding4;
  size_t p4;
  uint64_t fieldStartS642;
  size_t p5;
  uint64_t fieldStartptrT;
  size_t pos2;
  size_t p03;
  size_t p6;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t resultAfterptrT;
  uint8_t resultAfterS641;
  size_t p040;
  size_t m1;
  uint8_t *sub1;
  uint8_t first4;
  size_t pos_2;
  uint8_t first5;
  size_t pos_3;
  uint8_t first6;
  size_t pos_4;
  uint8_t first7;
  size_t pos_5;
  uint8_t first8;
  size_t pos_6;
  uint8_t first9;
  size_t pos_7;
  uint8_t first10;
  uint8_t first11;
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
  uint64_t n9;
  uint64_t bfirst9;
  uint64_t ptrT;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  size_t p70;
  uint64_t position;
  BOOLEAN actionSuccessPtrT;
  uint8_t *x0;
  size_t x1;
  size_t *x2;
  uint8_t res10;
  uint8_t resultAfterptrT1;
  size_t p7;
  uint64_t fieldStartS643;
  size_t pos3;
  size_t p04;
  size_t p8;
  size_t rem3;
  BOOLEAN hasBytes3;
  uint8_t res1;
  uint8_t resultAfterS642;
  size_t consumed;
  size_t p9;
  size_t p_0;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    resultAfters1 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfters1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfters1 == EVERPARSE_VALIDATOR_SUCCESS)
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
    s1 = bfirst2 + n2 * 256U;
    s1ConstraintIsOk = s1 <= Bound;
    if (s1ConstraintIsOk)
    {
      /* Validating field ___alignment_padding_4 */
      p2 = SlPos[0U];
      fieldStartS641 = (uint64_t)p2;
      pos1 = (size_t)0U;
      p02 = pos1;
      p3 = SlPos[0U];
      rem1 = SlLen - p3;
      hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
      if (hasBytes1)
      {
        pos1 = p02 + (size_t)4U;
        res = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (res == EVERPARSE_VALIDATOR_SUCCESS)
      {
        consumed0 = pos1;
        p40 = SlPos[0U];
        p_ = p40 + consumed0;
        SlPos[0U] = p_;
        resultAfterS640 = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterS640 = res;
      }
      if (resultAfterS640 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        resultAfterAlignmentPadding4 = resultAfterS640;
      }
      else
      {
        ErrorHandlerFn("_S64",
          "___alignment_padding_4",
          EverParseErrorReasonOfResult(resultAfterS640),
          resultAfterS640,
          Ctxt,
          SlBase,
          SlLen,
          SlPos,
          fieldStartS641);
        resultAfterAlignmentPadding4 = resultAfterS640;
      }
      if (resultAfterAlignmentPadding4 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        p4 = SlPos[0U];
        fieldStartS642 = (uint64_t)p4;
        p5 = SlPos[0U];
        fieldStartptrT = (uint64_t)p5;
        pos2 = (size_t)0U;
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        p03 = pos2;
        p6 = SlPos[0U];
        rem2 = SlLen - p6;
        hasBytes2 = p03 <= rem2 && (size_t)8U <= (rem2 - p03);
        if (hasBytes2)
        {
          pos2 = p03 + (size_t)8U;
          resultAfterptrT = EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAfterptrT = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (resultAfterptrT == EVERPARSE_VALIDATOR_SUCCESS)
        {
          p040 = SlPos[0U];
          m1 = p040 + (size_t)8U;
          sub1 = SlBase + p040;
          SlPos[0U] = m1;
          first4 = sub1[0U];
          pos_2 = (size_t)2U;
          first5 = sub1[1U];
          pos_3 = pos_2 + (size_t)1U;
          first6 = sub1[pos_2];
          pos_4 = pos_3 + (size_t)1U;
          first7 = sub1[pos_3];
          pos_5 = pos_4 + (size_t)1U;
          first8 = sub1[pos_4];
          pos_6 = pos_5 + (size_t)1U;
          first9 = sub1[pos_5];
          pos_7 = pos_6 + (size_t)1U;
          first10 = sub1[pos_6];
          first11 = sub1[pos_7];
          n3 = (uint64_t)(uint32_t)first11;
          bfirst3 = (uint64_t)(uint32_t)first10;
          n4 = bfirst3 + n3 * 256ULL;
          bfirst4 = (uint64_t)(uint32_t)first9;
          n5 = bfirst4 + n4 * 256ULL;
          bfirst5 = (uint64_t)(uint32_t)first8;
          n6 = bfirst5 + n5 * 256ULL;
          bfirst6 = (uint64_t)(uint32_t)first7;
          n7 = bfirst6 + n6 * 256ULL;
          bfirst7 = (uint64_t)(uint32_t)first6;
          n8 = bfirst7 + n7 * 256ULL;
          bfirst8 = (uint64_t)(uint32_t)first5;
          n9 = bfirst8 + n8 * 256ULL;
          bfirst9 = (uint64_t)(uint32_t)first4;
          ptrT = bfirst9 + n9 * 256ULL;
          readOffset = 0ULL;
          writeOffset = 0ULL;
          failed = FALSE;
          ok = ProbeInit1("_S64.ptrT", (uint64_t)8U, Dest);
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
              ptrT,
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
            p70 = EverParseStreamPos(Dest)[0U];
            position = (uint64_t)p70;
            ErrorHandlerFn("_S64",
              "ptrT",
              "probe",
              0U,
              Ctxt,
              EverParseStreamOf(Dest),
              EverParseStreamLen(Dest),
              EverParseStreamPos(Dest),
              position);
            b = 0ULL;
          }
          else
          {
            b = wr;
          }
          if (b != 0ULL)
          {
            EverParseStreamPos(Dest)[0U] = (size_t)0U;
            x0 = EverParseStreamOf(Dest);
            x1 = EverParseStreamLen(Dest);
            x2 = EverParseStreamPos(Dest);
            res10 = Specialize1ValidateT(s1, Ctxt, ErrorHandlerFn, x0, x1, x2);
            actionSuccessPtrT = res10 == EVERPARSE_VALIDATOR_SUCCESS;
          }
          else
          {
            ErrorHandlerFn("_S64",
              "ptrT",
              EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
              EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED,
              Ctxt,
              SlBase,
              SlLen,
              SlPos,
              fieldStartptrT);
            actionSuccessPtrT = FALSE;
          }
          resultAfterS641 =
            actionSuccessPtrT ? EVERPARSE_VALIDATOR_SUCCESS
                              : EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
        }
        else
        {
          resultAfterS641 = resultAfterptrT;
        }
        if (resultAfterS641 == EVERPARSE_VALIDATOR_SUCCESS)
        {
          resultAfterptrT1 = resultAfterS641;
        }
        else
        {
          ErrorHandlerFn("_S64",
            "ptrT",
            EverParseErrorReasonOfResult(resultAfterS641),
            resultAfterS641,
            Ctxt,
            SlBase,
            SlLen,
            SlPos,
            fieldStartS642);
          resultAfterptrT1 = resultAfterS641;
        }
        if (resultAfterptrT1 == EVERPARSE_VALIDATOR_SUCCESS)
        {
          p7 = SlPos[0U];
          fieldStartS643 = (uint64_t)p7;
          pos3 = (size_t)0U;
          p04 = pos3;
          p8 = SlPos[0U];
          rem3 = SlLen - p8;
          hasBytes3 = p04 <= rem3 && (size_t)8U <= (rem3 - p04);
          if (hasBytes3)
          {
            pos3 = p04 + (size_t)8U;
            res1 = EVERPARSE_VALIDATOR_SUCCESS;
          }
          else
          {
            res1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
          }
          if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
          {
            consumed = pos3;
            p9 = SlPos[0U];
            p_0 = p9 + consumed;
            SlPos[0U] = p_0;
            resultAfterS642 = EVERPARSE_VALIDATOR_SUCCESS;
          }
          else
          {
            resultAfterS642 = res1;
          }
          if (resultAfterS642 == EVERPARSE_VALIDATOR_SUCCESS)
          {
            resultAfterS64 = resultAfterS642;
          }
          else
          {
            ErrorHandlerFn("_S64",
              "s2",
              EverParseErrorReasonOfResult(resultAfterS642),
              resultAfterS642,
              Ctxt,
              SlBase,
              SlLen,
              SlPos,
              fieldStartS643);
            resultAfterS64 = resultAfterS642;
          }
        }
        else
        {
          resultAfterS64 = resultAfterptrT1;
        }
      }
      else
      {
        resultAfterS64 = resultAfterAlignmentPadding4;
      }
    }
    else
    {
      resultAfterS64 = EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
  }
  else
  {
    resultAfterS64 = resultAfters1;
  }
  if (resultAfterS64 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterS64;
  }
  ErrorHandlerFn("_S64",
    "s1",
    EverParseErrorReasonOfResult(resultAfterS64),
    resultAfterS64,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartS64);
  return resultAfterS64;
}

void
Specialize1Specialized32ProbeT(
  uint32_t Bound,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  size_t p;
  uint64_t position;
  KRML_MAYBE_UNUSED_VAR(Bound);
  Specialize1CopyBytes(8ULL,
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
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      "t1",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
}

inline uint8_t
Specialize1ValidateSpecializedR32(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  uint8_t resultAfterr1;
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
  uint32_t r1;
  size_t p2;
  uint64_t fieldStartSpecializedR32;
  size_t p3;
  uint64_t fieldStartptrS;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterptrS;
  uint8_t resultAfterSpecializedR32;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  uint8_t first4;
  size_t pos_2;
  uint8_t first5;
  size_t pos_3;
  uint8_t first6;
  uint8_t first7;
  uint32_t n3;
  uint32_t bfirst3;
  uint32_t n4;
  uint32_t bfirst4;
  uint32_t n5;
  uint32_t bfirst5;
  uint32_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  size_t p5;
  uint64_t position;
  BOOLEAN actionSuccessPtrS;
  uint8_t *x0;
  size_t x1;
  size_t *x2;
  uint8_t res1;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterr1 = res;
  }
  else
  {
    ErrorHandlerFn("___specialized_R32",
      "r1",
      EverParseErrorReasonOfResult(res),
      res,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    resultAfterr1 = res;
  }
  if (resultAfterr1 == EVERPARSE_VALIDATOR_SUCCESS)
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
    r1 = bfirst2 + n2 * 256U;
    p2 = SlPos[0U];
    fieldStartSpecializedR32 = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStartptrS = (uint64_t)p3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p4 = SlPos[0U];
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)4U;
      resultAfterptrS = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterptrS = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterptrS == EVERPARSE_VALIDATOR_SUCCESS)
    {
      p03 = SlPos[0U];
      m1 = p03 + (size_t)4U;
      sub1 = SlBase + p03;
      SlPos[0U] = m1;
      first4 = sub1[0U];
      pos_2 = (size_t)2U;
      first5 = sub1[1U];
      pos_3 = pos_2 + (size_t)1U;
      first6 = sub1[pos_2];
      first7 = sub1[pos_3];
      n3 = (uint32_t)first7;
      bfirst3 = (uint32_t)first6;
      n4 = bfirst3 + n3 * 256U;
      bfirst4 = (uint32_t)first5;
      n5 = bfirst4 + n4 * 256U;
      bfirst5 = (uint32_t)first4;
      ptrS = bfirst5 + n5 * 256U;
      src64 = UlongToPtr1(ptrS);
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit1("___specialized_R32.ptrS", (uint64_t)24U, DestS);
      if (ok)
      {
        Specialize1Specialized32ProbeS64(r1,
          "___specialized_R32",
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
        p5 = EverParseStreamPos(DestS)[0U];
        position = (uint64_t)p5;
        ErrorHandlerFn("___specialized_R32",
          "ptrS",
          "probe",
          0U,
          Ctxt,
          EverParseStreamOf(DestS),
          EverParseStreamLen(DestS),
          EverParseStreamPos(DestS),
          position);
        b = 0ULL;
      }
      else
      {
        b = wr;
      }
      if (b != 0ULL)
      {
        EverParseStreamPos(DestS)[0U] = (size_t)0U;
        x0 = EverParseStreamOf(DestS);
        x1 = EverParseStreamLen(DestS);
        x2 = EverParseStreamPos(DestS);
        res1 =
          Specialize1ValidateS64(Specialize1Specialized32ProbeT,
            r1,
            DestT,
            Ctxt,
            ErrorHandlerFn,
            x0,
            x1,
            x2);
        actionSuccessPtrS = res1 == EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("___specialized_R32",
          "ptrS",
          EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED,
          Ctxt,
          SlBase,
          SlLen,
          SlPos,
          fieldStartptrS);
        actionSuccessPtrS = FALSE;
      }
      resultAfterSpecializedR32 =
        actionSuccessPtrS ? EVERPARSE_VALIDATOR_SUCCESS
                          : EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterSpecializedR32 = resultAfterptrS;
    }
    if (resultAfterSpecializedR32 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterSpecializedR32;
    }
    ErrorHandlerFn("___specialized_R32",
      "ptrS",
      EverParseErrorReasonOfResult(resultAfterSpecializedR32),
      resultAfterSpecializedR32,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartSpecializedR32);
    return resultAfterSpecializedR32;
  }
  return resultAfterr1;
}

inline uint8_t
Specialize1ValidateR64(
  void
  (*ProbeS640)(
    uint32_t x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    EVERPARSE_STRING x3,
    uint8_t *x4,
    void
    (*x5)(
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
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    EVERPARSE_STRING x3,
    uint8_t *x4,
    void
    (*x5)(
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
  uint8_t resultAfterr1;
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
  uint32_t r1;
  size_t p2;
  uint64_t fieldStartR64;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res1;
  uint8_t resultAfterR64;
  size_t consumed;
  size_t p40;
  size_t p_;
  uint8_t resultAfterAlignmentPadding6;
  size_t p4;
  uint64_t fieldStartR641;
  size_t p5;
  uint64_t fieldStartptrS;
  size_t pos2;
  size_t p03;
  size_t p6;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t resultAfterptrS;
  uint8_t resultAfterR641;
  size_t p04;
  size_t m1;
  uint8_t *sub1;
  uint8_t first4;
  size_t pos_2;
  uint8_t first5;
  size_t pos_3;
  uint8_t first6;
  size_t pos_4;
  uint8_t first7;
  size_t pos_5;
  uint8_t first8;
  size_t pos_6;
  uint8_t first9;
  size_t pos_7;
  uint8_t first10;
  uint8_t first11;
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
  uint64_t n9;
  uint64_t bfirst9;
  uint64_t ptrS;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  size_t p7;
  uint64_t position;
  BOOLEAN actionSuccessPtrS;
  uint8_t *x0;
  size_t x1;
  size_t *x2;
  uint8_t res2;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterr1 = res;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "r1",
      EverParseErrorReasonOfResult(res),
      res,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    resultAfterr1 = res;
  }
  if (resultAfterr1 == EVERPARSE_VALIDATOR_SUCCESS)
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
    r1 = bfirst2 + n2 * 256U;
    /* Validating field ___alignment_padding_6 */
    p2 = SlPos[0U];
    fieldStartR64 = (uint64_t)p2;
    pos1 = (size_t)0U;
    p02 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)4U;
      res1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      consumed = pos1;
      p40 = SlPos[0U];
      p_ = p40 + consumed;
      SlPos[0U] = p_;
      resultAfterR64 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterR64 = res1;
    }
    if (resultAfterR64 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      resultAfterAlignmentPadding6 = resultAfterR64;
    }
    else
    {
      ErrorHandlerFn("_R64",
        "___alignment_padding_6",
        EverParseErrorReasonOfResult(resultAfterR64),
        resultAfterR64,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        fieldStartR64);
      resultAfterAlignmentPadding6 = resultAfterR64;
    }
    if (resultAfterAlignmentPadding6 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      p4 = SlPos[0U];
      fieldStartR641 = (uint64_t)p4;
      p5 = SlPos[0U];
      fieldStartptrS = (uint64_t)p5;
      pos2 = (size_t)0U;
      /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
      p03 = pos2;
      p6 = SlPos[0U];
      rem2 = SlLen - p6;
      hasBytes2 = p03 <= rem2 && (size_t)8U <= (rem2 - p03);
      if (hasBytes2)
      {
        pos2 = p03 + (size_t)8U;
        resultAfterptrS = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterptrS = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (resultAfterptrS == EVERPARSE_VALIDATOR_SUCCESS)
      {
        p04 = SlPos[0U];
        m1 = p04 + (size_t)8U;
        sub1 = SlBase + p04;
        SlPos[0U] = m1;
        first4 = sub1[0U];
        pos_2 = (size_t)2U;
        first5 = sub1[1U];
        pos_3 = pos_2 + (size_t)1U;
        first6 = sub1[pos_2];
        pos_4 = pos_3 + (size_t)1U;
        first7 = sub1[pos_3];
        pos_5 = pos_4 + (size_t)1U;
        first8 = sub1[pos_4];
        pos_6 = pos_5 + (size_t)1U;
        first9 = sub1[pos_5];
        pos_7 = pos_6 + (size_t)1U;
        first10 = sub1[pos_6];
        first11 = sub1[pos_7];
        n3 = (uint64_t)(uint32_t)first11;
        bfirst3 = (uint64_t)(uint32_t)first10;
        n4 = bfirst3 + n3 * 256ULL;
        bfirst4 = (uint64_t)(uint32_t)first9;
        n5 = bfirst4 + n4 * 256ULL;
        bfirst5 = (uint64_t)(uint32_t)first8;
        n6 = bfirst5 + n5 * 256ULL;
        bfirst6 = (uint64_t)(uint32_t)first7;
        n7 = bfirst6 + n6 * 256ULL;
        bfirst7 = (uint64_t)(uint32_t)first6;
        n8 = bfirst7 + n7 * 256ULL;
        bfirst8 = (uint64_t)(uint32_t)first5;
        n9 = bfirst8 + n8 * 256ULL;
        bfirst9 = (uint64_t)(uint32_t)first4;
        ptrS = bfirst9 + n9 * 256ULL;
        readOffset = 0ULL;
        writeOffset = 0ULL;
        failed = FALSE;
        ok = ProbeInit1("_R64.ptrS", (uint64_t)24U, DestS);
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
            ptrS,
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
          p7 = EverParseStreamPos(DestS)[0U];
          position = (uint64_t)p7;
          ErrorHandlerFn("_R64",
            "ptrS",
            "probe",
            0U,
            Ctxt,
            EverParseStreamOf(DestS),
            EverParseStreamLen(DestS),
            EverParseStreamPos(DestS),
            position);
          b = 0ULL;
        }
        else
        {
          b = wr;
        }
        if (b != 0ULL)
        {
          EverParseStreamPos(DestS)[0U] = (size_t)0U;
          x0 = EverParseStreamOf(DestS);
          x1 = EverParseStreamLen(DestS);
          x2 = EverParseStreamPos(DestS);
          res2 = Specialize1ValidateS64(ProbeS640, r1, DestT, Ctxt, ErrorHandlerFn, x0, x1, x2);
          actionSuccessPtrS = res2 == EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          ErrorHandlerFn("_R64",
            "ptrS",
            EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
            EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED,
            Ctxt,
            SlBase,
            SlLen,
            SlPos,
            fieldStartptrS);
          actionSuccessPtrS = FALSE;
        }
        resultAfterR641 =
          actionSuccessPtrS ? EVERPARSE_VALIDATOR_SUCCESS
                            : EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
      }
      else
      {
        resultAfterR641 = resultAfterptrS;
      }
      if (resultAfterR641 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        return resultAfterR641;
      }
      ErrorHandlerFn("_R64",
        "ptrS",
        EverParseErrorReasonOfResult(resultAfterR641),
        resultAfterR641,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        fieldStartR641);
      return resultAfterR641;
    }
    return resultAfterAlignmentPadding6;
  }
  return resultAfterr1;
}

void
Specialize1RProbeFieldR640T(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  size_t p;
  uint64_t position;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Fd);
  hasFailed = Failed[0U];
  if (hasFailed)
  {
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      "probe_and_copy_init_sz",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
  rd = ReadOffset[0U];
  wr = WriteOffset[0U];
  ok = ProbeAndCopy1(Sz, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Sz;
    WriteOffset[0U] = wr + Sz;
    return;
  }
  Failed[0U] = TRUE;
}

void
Specialize1RProbeFieldR641S64(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  size_t p;
  uint64_t position;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Fd);
  hasFailed = Failed[0U];
  if (hasFailed)
  {
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      "probe_and_copy_init_sz",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
  rd = ReadOffset[0U];
  wr = WriteOffset[0U];
  ok = ProbeAndCopy1(Sz, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Sz;
    WriteOffset[0U] = wr + Sz;
    return;
  }
  Failed[0U] = TRUE;
}

uint8_t
Specialize1ValidateR(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  size_t p0;
  uint64_t fieldStartR;
  uint8_t resultAfterR;
  size_t p;
  uint64_t fieldStartR0;
  uint8_t resultAfterR0;
  if (Requestor32)
  {
    /* Validating field r32 */
    p0 = SlPos[0U];
    fieldStartR = (uint64_t)p0;
    resultAfterR =
      Specialize1ValidateSpecializedR32(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        SlBase,
        SlLen,
        SlPos);
    if (resultAfterR == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterR;
    }
    ErrorHandlerFn("___R",
      "r32",
      EverParseErrorReasonOfResult(resultAfterR),
      resultAfterR,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartR);
    return resultAfterR;
  }
  /* Validating field r64 */
  p = SlPos[0U];
  fieldStartR0 = (uint64_t)p;
  resultAfterR0 =
    Specialize1ValidateR64(Specialize1RProbeFieldR640T,
      Specialize1RProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      SlBase,
      SlLen,
      SlPos);
  if (resultAfterR0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterR0;
  }
  ErrorHandlerFn("___R",
    "r64",
    EverParseErrorReasonOfResult(resultAfterR0),
    resultAfterR0,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartR0);
  return resultAfterR0;
}

void
Specialize1R32AttemptProbePtrSS32attempt(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  size_t p;
  uint64_t position;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Fd);
  hasFailed = Failed[0U];
  if (hasFailed)
  {
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      "probe_and_copy_init_sz",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
  rd = ReadOffset[0U];
  wr = WriteOffset[0U];
  ok = ProbeAndCopy1(Sz, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Sz;
    WriteOffset[0U] = wr + Sz;
    return;
  }
  Failed[0U] = TRUE;
}

void
Specialize1S32attemptProbePtrTT(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  size_t p;
  uint64_t position;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Fd);
  hasFailed = Failed[0U];
  if (hasFailed)
  {
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      "probe_and_copy_init_sz",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
  rd = ReadOffset[0U];
  wr = WriteOffset[0U];
  ok = ProbeAndCopy1(Sz, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Sz;
    WriteOffset[0U] = wr + Sz;
    return;
  }
  Failed[0U] = TRUE;
}

inline uint8_t
Specialize1ValidateS32Attempt(
  uint32_t Bound,
  EVERPARSE_COPY_BUFFER_T Dest,
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
  uint64_t fieldStartS32Attempt = (uint64_t)p;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t resultAfterf;
  uint8_t resultAfterS32Attempt;
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
  uint32_t f;
  BOOLEAN fConstraintIsOk;
  size_t p2;
  uint64_t fieldStartS32Attempt1;
  size_t p3;
  uint64_t fieldStartptrT;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterptrT;
  uint8_t resultAfterS32Attempt0;
  size_t p030;
  size_t m1;
  uint8_t *sub1;
  uint8_t first4;
  size_t pos_2;
  uint8_t first5;
  size_t pos_3;
  uint8_t first6;
  uint8_t first7;
  uint32_t n3;
  uint32_t bfirst3;
  uint32_t n4;
  uint32_t bfirst4;
  uint32_t n5;
  uint32_t bfirst5;
  uint32_t ptrT;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  size_t p50;
  uint64_t position;
  BOOLEAN actionSuccessPtrT;
  uint8_t *x0;
  size_t x1;
  size_t *x2;
  uint8_t res0;
  uint8_t resultAfterptrT1;
  size_t pos2;
  size_t p5;
  uint64_t viewStart;
  size_t fieldOff;
  uint64_t startPos;
  size_t p03;
  size_t p6;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t res;
  uint8_t res1;
  size_t consumed;
  size_t p7;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    resultAfterf = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterf = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterf == EVERPARSE_VALIDATOR_SUCCESS)
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
    f = bfirst2 + n2 * 256U;
    fConstraintIsOk = f <= Bound;
    if (fConstraintIsOk)
    {
      p2 = SlPos[0U];
      fieldStartS32Attempt1 = (uint64_t)p2;
      p3 = SlPos[0U];
      fieldStartptrT = (uint64_t)p3;
      pos1 = (size_t)0U;
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      p02 = pos1;
      p4 = SlPos[0U];
      rem1 = SlLen - p4;
      hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
      if (hasBytes1)
      {
        pos1 = p02 + (size_t)4U;
        resultAfterptrT = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterptrT = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (resultAfterptrT == EVERPARSE_VALIDATOR_SUCCESS)
      {
        p030 = SlPos[0U];
        m1 = p030 + (size_t)4U;
        sub1 = SlBase + p030;
        SlPos[0U] = m1;
        first4 = sub1[0U];
        pos_2 = (size_t)2U;
        first5 = sub1[1U];
        pos_3 = pos_2 + (size_t)1U;
        first6 = sub1[pos_2];
        first7 = sub1[pos_3];
        n3 = (uint32_t)first7;
        bfirst3 = (uint32_t)first6;
        n4 = bfirst3 + n3 * 256U;
        bfirst4 = (uint32_t)first5;
        n5 = bfirst4 + n4 * 256U;
        bfirst5 = (uint32_t)first4;
        ptrT = bfirst5 + n5 * 256U;
        src64 = UlongToPtr1(ptrT);
        readOffset = 0ULL;
        writeOffset = 0ULL;
        failed = FALSE;
        ok = ProbeInit1("_S32_Attempt.ptrT", (uint64_t)8U, Dest);
        if (ok)
        {
          Specialize1S32attemptProbePtrTT(f,
            "_S32_Attempt",
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
          p50 = EverParseStreamPos(Dest)[0U];
          position = (uint64_t)p50;
          ErrorHandlerFn("_S32_Attempt",
            "ptrT",
            "probe",
            0U,
            Ctxt,
            EverParseStreamOf(Dest),
            EverParseStreamLen(Dest),
            EverParseStreamPos(Dest),
            position);
          b = 0ULL;
        }
        else
        {
          b = wr;
        }
        if (b != 0ULL)
        {
          EverParseStreamPos(Dest)[0U] = (size_t)0U;
          x0 = EverParseStreamOf(Dest);
          x1 = EverParseStreamLen(Dest);
          x2 = EverParseStreamPos(Dest);
          res0 = Specialize1ValidateT(f, Ctxt, ErrorHandlerFn, x0, x1, x2);
          actionSuccessPtrT = res0 == EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          ErrorHandlerFn("_S32_Attempt",
            "ptrT",
            EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
            EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED,
            Ctxt,
            SlBase,
            SlLen,
            SlPos,
            fieldStartptrT);
          actionSuccessPtrT = FALSE;
        }
        resultAfterS32Attempt0 =
          actionSuccessPtrT ? EVERPARSE_VALIDATOR_SUCCESS
                            : EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
      }
      else
      {
        resultAfterS32Attempt0 = resultAfterptrT;
      }
      if (resultAfterS32Attempt0 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        resultAfterptrT1 = resultAfterS32Attempt0;
      }
      else
      {
        ErrorHandlerFn("_S32_Attempt",
          "ptrT",
          EverParseErrorReasonOfResult(resultAfterS32Attempt0),
          resultAfterS32Attempt0,
          Ctxt,
          SlBase,
          SlLen,
          SlPos,
          fieldStartS32Attempt1);
        resultAfterptrT1 = resultAfterS32Attempt0;
      }
      if (resultAfterptrT1 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        pos2 = (size_t)0U;
        /* Validating field g */
        p5 = SlPos[0U];
        viewStart = (uint64_t)p5;
        fieldOff = pos2;
        startPos = viewStart + (uint64_t)fieldOff;
        /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
        p03 = pos2;
        p6 = SlPos[0U];
        rem2 = SlLen - p6;
        hasBytes2 = p03 <= rem2 && (size_t)4U <= (rem2 - p03);
        if (hasBytes2)
        {
          pos2 = p03 + (size_t)4U;
          res = EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (res == EVERPARSE_VALIDATOR_SUCCESS)
        {
          res1 = res;
        }
        else
        {
          ErrorHandlerFn("_S32_Attempt",
            "g",
            EverParseErrorReasonOfResult(res),
            res,
            Ctxt,
            SlBase,
            SlLen,
            SlPos,
            startPos);
          res1 = res;
        }
        if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
        {
          consumed = pos2;
          p7 = SlPos[0U];
          p_ = p7 + consumed;
          SlPos[0U] = p_;
          resultAfterS32Attempt = EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAfterS32Attempt = res1;
        }
      }
      else
      {
        resultAfterS32Attempt = resultAfterptrT1;
      }
    }
    else
    {
      resultAfterS32Attempt = EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
  }
  else
  {
    resultAfterS32Attempt = resultAfterf;
  }
  if (resultAfterS32Attempt == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterS32Attempt;
  }
  ErrorHandlerFn("_S32_Attempt",
    "f",
    EverParseErrorReasonOfResult(resultAfterS32Attempt),
    resultAfterS32Attempt,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartS32Attempt);
  return resultAfterS32Attempt;
}

inline uint8_t
Specialize1ValidateR32Attempt(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  uint8_t resultAfterf;
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
  uint32_t f;
  size_t p2;
  uint64_t fieldStartR32Attempt;
  size_t p3;
  uint64_t fieldStartptrS;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterptrS;
  uint8_t resultAfterR32Attempt;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  uint8_t first4;
  size_t pos_2;
  uint8_t first5;
  size_t pos_3;
  uint8_t first6;
  uint8_t first7;
  uint32_t n3;
  uint32_t bfirst3;
  uint32_t n4;
  uint32_t bfirst4;
  uint32_t n5;
  uint32_t bfirst5;
  uint32_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  size_t p5;
  uint64_t position;
  BOOLEAN actionSuccessPtrS;
  uint8_t *x0;
  size_t x1;
  size_t *x2;
  uint8_t res1;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterf = res;
  }
  else
  {
    ErrorHandlerFn("_R32_Attempt",
      "f",
      EverParseErrorReasonOfResult(res),
      res,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    resultAfterf = res;
  }
  if (resultAfterf == EVERPARSE_VALIDATOR_SUCCESS)
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
    f = bfirst2 + n2 * 256U;
    p2 = SlPos[0U];
    fieldStartR32Attempt = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStartptrS = (uint64_t)p3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p4 = SlPos[0U];
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)4U;
      resultAfterptrS = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterptrS = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterptrS == EVERPARSE_VALIDATOR_SUCCESS)
    {
      p03 = SlPos[0U];
      m1 = p03 + (size_t)4U;
      sub1 = SlBase + p03;
      SlPos[0U] = m1;
      first4 = sub1[0U];
      pos_2 = (size_t)2U;
      first5 = sub1[1U];
      pos_3 = pos_2 + (size_t)1U;
      first6 = sub1[pos_2];
      first7 = sub1[pos_3];
      n3 = (uint32_t)first7;
      bfirst3 = (uint32_t)first6;
      n4 = bfirst3 + n3 * 256U;
      bfirst4 = (uint32_t)first5;
      n5 = bfirst4 + n4 * 256U;
      bfirst5 = (uint32_t)first4;
      ptrS = bfirst5 + n5 * 256U;
      src64 = UlongToPtr1(ptrS);
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit1("_R32_Attempt.ptrS", (uint64_t)12U, DestS);
      if (ok)
      {
        Specialize1R32AttemptProbePtrSS32attempt(f,
          "_R32_Attempt",
          "ptrS",
          "probe",
          Ctxt,
          ErrorHandlerFn,
          &readOffset,
          &writeOffset,
          &failed,
          src64,
          (uint64_t)12U,
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
        p5 = EverParseStreamPos(DestS)[0U];
        position = (uint64_t)p5;
        ErrorHandlerFn("_R32_Attempt",
          "ptrS",
          "probe",
          0U,
          Ctxt,
          EverParseStreamOf(DestS),
          EverParseStreamLen(DestS),
          EverParseStreamPos(DestS),
          position);
        b = 0ULL;
      }
      else
      {
        b = wr;
      }
      if (b != 0ULL)
      {
        EverParseStreamPos(DestS)[0U] = (size_t)0U;
        x0 = EverParseStreamOf(DestS);
        x1 = EverParseStreamLen(DestS);
        x2 = EverParseStreamPos(DestS);
        res1 = Specialize1ValidateS32Attempt(f, DestT, Ctxt, ErrorHandlerFn, x0, x1, x2);
        actionSuccessPtrS = res1 == EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("_R32_Attempt",
          "ptrS",
          EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED,
          Ctxt,
          SlBase,
          SlLen,
          SlPos,
          fieldStartptrS);
        actionSuccessPtrS = FALSE;
      }
      resultAfterR32Attempt =
        actionSuccessPtrS ? EVERPARSE_VALIDATOR_SUCCESS
                          : EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterR32Attempt = resultAfterptrS;
    }
    if (resultAfterR32Attempt == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterR32Attempt;
    }
    ErrorHandlerFn("_R32_Attempt",
      "ptrS",
      EverParseErrorReasonOfResult(resultAfterR32Attempt),
      resultAfterR32Attempt,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartR32Attempt);
    return resultAfterR32Attempt;
  }
  return resultAfterf;
}

void
Specialize1RmuxProbeFieldR640T(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  size_t p;
  uint64_t position;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Fd);
  hasFailed = Failed[0U];
  if (hasFailed)
  {
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      "probe_and_copy_init_sz",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
  rd = ReadOffset[0U];
  wr = WriteOffset[0U];
  ok = ProbeAndCopy1(Sz, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Sz;
    WriteOffset[0U] = wr + Sz;
    return;
  }
  Failed[0U] = TRUE;
}

void
Specialize1RmuxProbeFieldR641S64(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
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
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  size_t p;
  uint64_t position;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Fd);
  hasFailed = Failed[0U];
  if (hasFailed)
  {
    p = EverParseStreamPos(Dest)[0U];
    position = (uint64_t)p;
    Err(Tn,
      Fn,
      "probe_and_copy_init_sz",
      0U,
      Ctxt,
      EverParseStreamOf(Dest),
      EverParseStreamLen(Dest),
      EverParseStreamPos(Dest),
      position);
    return;
  }
  rd = ReadOffset[0U];
  wr = WriteOffset[0U];
  ok = ProbeAndCopy1(Sz, rd, wr, Src, Dest);
  if (ok)
  {
    ReadOffset[0U] = rd + Sz;
    WriteOffset[0U] = wr + Sz;
    return;
  }
  Failed[0U] = TRUE;
}

uint8_t
Specialize1ValidateRmux(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  size_t p0;
  uint64_t fieldStartRmux;
  uint8_t resultAfterRmux;
  size_t p;
  uint64_t fieldStartRmux0;
  uint8_t resultAfterRmux0;
  if (Requestor32)
  {
    /* Validating field r32 */
    p0 = SlPos[0U];
    fieldStartRmux = (uint64_t)p0;
    resultAfterRmux =
      Specialize1ValidateR32Attempt(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        SlBase,
        SlLen,
        SlPos);
    if (resultAfterRmux == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterRmux;
    }
    ErrorHandlerFn("_RMux",
      "r32",
      EverParseErrorReasonOfResult(resultAfterRmux),
      resultAfterRmux,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartRmux);
    return resultAfterRmux;
  }
  /* Validating field r64 */
  p = SlPos[0U];
  fieldStartRmux0 = (uint64_t)p;
  resultAfterRmux0 =
    Specialize1ValidateR64(Specialize1RmuxProbeFieldR640T,
      Specialize1RmuxProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      SlBase,
      SlLen,
      SlPos);
  if (resultAfterRmux0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterRmux0;
  }
  ErrorHandlerFn("_RMux",
    "r64",
    EverParseErrorReasonOfResult(resultAfterRmux0),
    resultAfterRmux0,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartRmux0);
  return resultAfterRmux0;
}

