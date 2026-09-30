

#include "Specialize1.h"

#include "Specialize1_ExternalAPI.h"
#include "EverParse.h"

static inline uint64_t
ValidateT(
  uint32_t Bound,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field t1 */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytesForT1 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterT10;
  uint64_t res;
  uint64_t positionAfterT1;
  BOOLEAN hasBytesForT2_refinement;
  uint64_t positionAfterT2_refinement;
  uint64_t positionAfterT2_refinement0;
  uint32_t t2_refinement;
  BOOLEAN t2_refinementConstraintIsOk;
  if (hasBytesForT1)
  {
    positionAfterT10 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterT10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterT10))
  {
    res = positionAfterT10;
  }
  else
  {
    ErrorHandlerFn("_T",
      "t1",
      EverParseErrorReasonOfResult(positionAfterT10),
      EverParseGetValidatorErrorKind(positionAfterT10),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterT10;
  }
  positionAfterT1 = res;
  if (EverParseIsError(positionAfterT1))
  {
    return positionAfterT1;
  }
  /* Validating field t2 */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytesForT2_refinement = (InputLength - positionAfterT1) >= 4ULL;
  if (hasBytesForT2_refinement)
  {
    positionAfterT2_refinement = positionAfterT1 + 4ULL;
  }
  else
  {
    positionAfterT2_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterT1);
  }
  if (EverParseIsError(positionAfterT2_refinement))
  {
    positionAfterT2_refinement0 = positionAfterT2_refinement;
  }
  else
  {
    /* reading field_value */
    t2_refinement = Load32Le(Input + (uint32_t)positionAfterT1);
    /* start: checking constraint */
    t2_refinementConstraintIsOk = t2_refinement <= Bound;
    /* end: checking constraint */
    positionAfterT2_refinement0 =
      EverParseCheckConstraintOk(t2_refinementConstraintIsOk,
        positionAfterT2_refinement);
  }
  if (EverParseIsSuccess(positionAfterT2_refinement0))
  {
    return positionAfterT2_refinement0;
  }
  ErrorHandlerFn("_T",
    "t2.refinement",
    EverParseErrorReasonOfResult(positionAfterT2_refinement0),
    EverParseGetValidatorErrorKind(positionAfterT2_refinement0),
    Ctxt,
    Input,
    positionAfterT1);
  return positionAfterT2_refinement0;
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
  BOOLEAN ok = ProbeAndCopy1(Numbytes, rd, wr, Src, Dest);
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
  EVERPARSE_STRING Fieldname,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
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
  uint32_t v = ProbeAndReadU321(Failed, rd, Src, Dest);
  BOOLEAN hasFailed = *Failed;
  uint32_t res1;
  BOOLEAN hasFailed0;
  uint64_t res11;
  BOOLEAN hasFailed1;
  uint64_t wr;
  BOOLEAN ok;
  if (hasFailed)
  {
    Err(Tn, Fn, Det, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
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
  res11 = UlongToPtr1(res1);
  hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, Fieldname, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  wr = *WriteOffset;
  ok = WriteU641(res11, wr, Dest);
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
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
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
  KRML_MAYBE_UNUSED_VAR(Det);
  KRML_MAYBE_UNUSED_VAR(Sz);
  CopyBytes(8ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "t1", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint64_t
ValidateS64(
  void
  (*ProbePtrT)(
    uint32_t x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    EVERPARSE_STRING x3,
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
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytesForS1 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterS10;
  uint64_t positionAfterS1;
  uint32_t s1;
  BOOLEAN s1ConstraintIsOk;
  uint64_t positionAfterCheckedS1;
  BOOLEAN hasBytesForAlignmentPadding4;
  uint64_t res0;
  uint64_t positionAfterAlignmentPadding4;
  uint64_t positionAfterAlignmentPadding40;
  BOOLEAN hasBytesForPtrT;
  uint64_t positionAfterPtrT0;
  uint64_t positionAfterPtrT1;
  uint64_t ptrT;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint64_t result;
  uint64_t positionAfterPtrT;
  BOOLEAN hasBytesForS2;
  uint64_t res;
  uint64_t positionAfterS2;
  if (hasBytesForS1)
  {
    positionAfterS10 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterS10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterS10))
  {
    positionAfterS1 = positionAfterS10;
  }
  else
  {
    s1 = Load32Le(Input + (uint32_t)StartPosition);
    s1ConstraintIsOk = s1 <= Bound;
    positionAfterCheckedS1 = EverParseCheckConstraintOk(s1ConstraintIsOk, positionAfterS10);
    if (EverParseIsError(positionAfterCheckedS1))
    {
      positionAfterS1 = positionAfterCheckedS1;
    }
    else
    {
      /* Validating field ___alignment_padding_4 */
      hasBytesForAlignmentPadding4 = (InputLength - positionAfterCheckedS1) >= (uint64_t)4U;
      if (hasBytesForAlignmentPadding4)
      {
        res0 = positionAfterCheckedS1 + (uint64_t)4U;
      }
      else
      {
        res0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedS1);
      }
      positionAfterAlignmentPadding4 = res0;
      if (EverParseIsSuccess(positionAfterAlignmentPadding4))
      {
        positionAfterAlignmentPadding40 = positionAfterAlignmentPadding4;
      }
      else
      {
        ErrorHandlerFn("_S64",
          "___alignment_padding_4",
          EverParseErrorReasonOfResult(positionAfterAlignmentPadding4),
          EverParseGetValidatorErrorKind(positionAfterAlignmentPadding4),
          Ctxt,
          Input,
          positionAfterCheckedS1);
        positionAfterAlignmentPadding40 = positionAfterAlignmentPadding4;
      }
      if (EverParseIsError(positionAfterAlignmentPadding40))
      {
        positionAfterS1 = positionAfterAlignmentPadding40;
      }
      else
      {
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        hasBytesForPtrT = (InputLength - positionAfterAlignmentPadding40) >= 8ULL;
        if (hasBytesForPtrT)
        {
          positionAfterPtrT0 = positionAfterAlignmentPadding40 + 8ULL;
        }
        else
        {
          positionAfterPtrT0 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAfterAlignmentPadding40);
        }
        if (EverParseIsError(positionAfterPtrT0))
        {
          positionAfterPtrT1 = positionAfterPtrT0;
        }
        else
        {
          ptrT = Load64Le(Input + (uint32_t)positionAfterAlignmentPadding40);
          src64 = ptrT;
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
            result =
              ValidateT(s1,
                Ctxt,
                ErrorHandlerFn,
                EverParseStreamOf(Dest),
                EverParseStreamLen(Dest),
                0ULL);
            actionResult = !EverParseIsError(result);
          }
          else
          {
            ErrorHandlerFn("_S64",
              "ptrT",
              EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
              EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
              Ctxt,
              Input,
              positionAfterAlignmentPadding40);
            actionResult = FALSE;
          }
          if (actionResult)
          {
            positionAfterPtrT1 = positionAfterPtrT0;
          }
          else
          {
            positionAfterPtrT1 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
                positionAfterPtrT0);
          }
        }
        if (EverParseIsSuccess(positionAfterPtrT1))
        {
          positionAfterPtrT = positionAfterPtrT1;
        }
        else
        {
          ErrorHandlerFn("_S64",
            "ptrT",
            EverParseErrorReasonOfResult(positionAfterPtrT1),
            EverParseGetValidatorErrorKind(positionAfterPtrT1),
            Ctxt,
            Input,
            positionAfterAlignmentPadding40);
          positionAfterPtrT = positionAfterPtrT1;
        }
        if (EverParseIsError(positionAfterPtrT))
        {
          positionAfterS1 = positionAfterPtrT;
        }
        else
        {
          hasBytesForS2 = (InputLength - positionAfterPtrT) >= 8ULL;
          if (hasBytesForS2)
          {
            res = positionAfterPtrT + 8ULL;
          }
          else
          {
            res =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterPtrT);
          }
          positionAfterS2 = res;
          if (EverParseIsSuccess(positionAfterS2))
          {
            positionAfterS1 = positionAfterS2;
          }
          else
          {
            ErrorHandlerFn("_S64",
              "s2",
              EverParseErrorReasonOfResult(positionAfterS2),
              EverParseGetValidatorErrorKind(positionAfterS2),
              Ctxt,
              Input,
              positionAfterPtrT);
            positionAfterS1 = positionAfterS2;
          }
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfterS1))
  {
    return positionAfterS1;
  }
  ErrorHandlerFn("_S64",
    "s1",
    EverParseErrorReasonOfResult(positionAfterS1),
    EverParseGetValidatorErrorKind(positionAfterS1),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterS1;
}

static void
Specialized32ProbeS64(
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
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
    Det,
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

static inline uint64_t
ValidateR64(
  void
  (*ProbeS640)(
    uint32_t x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    EVERPARSE_STRING x3,
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
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    EVERPARSE_STRING x3,
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
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytesForR1 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterR10;
  uint64_t positionAfterR1;
  uint32_t r1;
  BOOLEAN hasBytesForAlignmentPadding6;
  uint64_t res;
  uint64_t positionAfterAlignmentPadding6;
  uint64_t positionAfterAlignmentPadding60;
  BOOLEAN hasBytesForPtrS;
  uint64_t positionAfterPtrS0;
  uint64_t positionAfterPtrS;
  uint64_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint64_t result;
  if (hasBytesForR1)
  {
    positionAfterR10 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterR10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterR10))
  {
    positionAfterR1 = positionAfterR10;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "r1",
      EverParseErrorReasonOfResult(positionAfterR10),
      EverParseGetValidatorErrorKind(positionAfterR10),
      Ctxt,
      Input,
      StartPosition);
    positionAfterR1 = positionAfterR10;
  }
  if (EverParseIsError(positionAfterR1))
  {
    return positionAfterR1;
  }
  r1 = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field ___alignment_padding_6 */
  hasBytesForAlignmentPadding6 = (InputLength - positionAfterR1) >= (uint64_t)4U;
  if (hasBytesForAlignmentPadding6)
  {
    res = positionAfterR1 + (uint64_t)4U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, positionAfterR1);
  }
  positionAfterAlignmentPadding6 = res;
  if (EverParseIsSuccess(positionAfterAlignmentPadding6))
  {
    positionAfterAlignmentPadding60 = positionAfterAlignmentPadding6;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "___alignment_padding_6",
      EverParseErrorReasonOfResult(positionAfterAlignmentPadding6),
      EverParseGetValidatorErrorKind(positionAfterAlignmentPadding6),
      Ctxt,
      Input,
      positionAfterR1);
    positionAfterAlignmentPadding60 = positionAfterAlignmentPadding6;
  }
  if (EverParseIsError(positionAfterAlignmentPadding60))
  {
    return positionAfterAlignmentPadding60;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForPtrS = (InputLength - positionAfterAlignmentPadding60) >= 8ULL;
  if (hasBytesForPtrS)
  {
    positionAfterPtrS0 = positionAfterAlignmentPadding60 + 8ULL;
  }
  else
  {
    positionAfterPtrS0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterAlignmentPadding60);
  }
  if (EverParseIsError(positionAfterPtrS0))
  {
    positionAfterPtrS = positionAfterPtrS0;
  }
  else
  {
    ptrS = Load64Le(Input + (uint32_t)positionAfterAlignmentPadding60);
    src64 = ptrS;
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
      result =
        ValidateS64(ProbeS640,
          r1,
          DestT,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestS),
          EverParseStreamLen(DestS),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_R64",
        "ptrS",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAfterAlignmentPadding60);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterPtrS = positionAfterPtrS0;
    }
    else
    {
      positionAfterPtrS =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtrS0);
    }
  }
  if (EverParseIsSuccess(positionAfterPtrS))
  {
    return positionAfterPtrS;
  }
  ErrorHandlerFn("_R64",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterPtrS),
    EverParseGetValidatorErrorKind(positionAfterPtrS),
    Ctxt,
    Input,
    positionAfterAlignmentPadding60);
  return positionAfterPtrS;
}

static inline uint64_t
ValidateSpecializedR32(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytesForR1 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterR10;
  uint64_t positionAfterR1;
  uint32_t r1;
  BOOLEAN hasBytesForPtrS;
  uint64_t positionAfterPtrS0;
  uint64_t positionAfterPtrS;
  uint32_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint64_t result;
  if (hasBytesForR1)
  {
    positionAfterR10 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterR10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterR10))
  {
    positionAfterR1 = positionAfterR10;
  }
  else
  {
    ErrorHandlerFn("___specialized_R32",
      "r1",
      EverParseErrorReasonOfResult(positionAfterR10),
      EverParseGetValidatorErrorKind(positionAfterR10),
      Ctxt,
      Input,
      StartPosition);
    positionAfterR1 = positionAfterR10;
  }
  if (EverParseIsError(positionAfterR1))
  {
    return positionAfterR1;
  }
  r1 = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytesForPtrS = (InputLength - positionAfterR1) >= 4ULL;
  if (hasBytesForPtrS)
  {
    positionAfterPtrS0 = positionAfterR1 + 4ULL;
  }
  else
  {
    positionAfterPtrS0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterR1);
  }
  if (EverParseIsError(positionAfterPtrS0))
  {
    positionAfterPtrS = positionAfterPtrS0;
  }
  else
  {
    ptrS = Load32Le(Input + (uint32_t)positionAfterR1);
    src64 = UlongToPtr1(ptrS);
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    ok = ProbeInit1("___specialized_R32.ptrS", (uint64_t)24U, DestS);
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
      result =
        ValidateS64(Specialized32ProbeT,
          r1,
          DestT,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestS),
          EverParseStreamLen(DestS),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("___specialized_R32",
        "ptrS",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAfterR1);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterPtrS = positionAfterPtrS0;
    }
    else
    {
      positionAfterPtrS =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtrS0);
    }
  }
  if (EverParseIsSuccess(positionAfterPtrS))
  {
    return positionAfterPtrS;
  }
  ErrorHandlerFn("___specialized_R32",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterPtrS),
    EverParseGetValidatorErrorKind(positionAfterPtrS),
    Ctxt,
    Input,
    positionAfterR1);
  return positionAfterPtrS;
}

static void
RProbeFieldR640T(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
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
  KRML_MAYBE_UNUSED_VAR(Det);
  res1 = Sz;
  hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  rd = *ReadOffset;
  wr = *WriteOffset;
  ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
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
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
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
  KRML_MAYBE_UNUSED_VAR(Det);
  res1 = Sz;
  hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  rd = *ReadOffset;
  wr = *WriteOffset;
  ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

uint64_t
Specialize1ValidateR(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  uint64_t positionAfterR32;
  uint64_t positionAfterR64;
  if (Requestor32)
  {
    /* Validating field r32 */
    positionAfterR32 =
      ValidateSpecializedR32(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterR32))
    {
      return positionAfterR32;
    }
    ErrorHandlerFn("___R",
      "r32",
      EverParseErrorReasonOfResult(positionAfterR32),
      EverParseGetValidatorErrorKind(positionAfterR32),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterR32;
  }
  /* Validating field r64 */
  positionAfterR64 =
    ValidateR64(RProbeFieldR640T,
      RProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterR64))
  {
    return positionAfterR64;
  }
  ErrorHandlerFn("___R",
    "r64",
    EverParseErrorReasonOfResult(positionAfterR64),
    EverParseGetValidatorErrorKind(positionAfterR64),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterR64;
}

static void
S32attemptProbePtrTT(
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
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
  uint64_t res1 = Sz;
  BOOLEAN hasFailed = *Failed;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  rd = *ReadOffset;
  wr = *WriteOffset;
  ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

static inline uint64_t
ValidateS32Attempt(
  uint32_t Bound,
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytesForF = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterF0;
  uint64_t positionAfterF;
  uint32_t f;
  BOOLEAN fConstraintIsOk;
  uint64_t positionAfterCheckedF;
  BOOLEAN hasBytesForPtrT;
  uint64_t positionAfterPtrT0;
  uint64_t positionAfterPtrT1;
  uint32_t ptrT;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint64_t result;
  uint64_t positionAfterPtrT;
  BOOLEAN hasBytesForG;
  uint64_t positionAfterG;
  uint64_t res;
  if (hasBytesForF)
  {
    positionAfterF0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterF0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterF0))
  {
    positionAfterF = positionAfterF0;
  }
  else
  {
    f = Load32Le(Input + (uint32_t)StartPosition);
    fConstraintIsOk = f <= Bound;
    positionAfterCheckedF = EverParseCheckConstraintOk(fConstraintIsOk, positionAfterF0);
    if (EverParseIsError(positionAfterCheckedF))
    {
      positionAfterF = positionAfterCheckedF;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      hasBytesForPtrT = (InputLength - positionAfterCheckedF) >= 4ULL;
      if (hasBytesForPtrT)
      {
        positionAfterPtrT0 = positionAfterCheckedF + 4ULL;
      }
      else
      {
        positionAfterPtrT0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedF);
      }
      if (EverParseIsError(positionAfterPtrT0))
      {
        positionAfterPtrT1 = positionAfterPtrT0;
      }
      else
      {
        ptrT = Load32Le(Input + (uint32_t)positionAfterCheckedF);
        src64 = UlongToPtr1(ptrT);
        readOffset = 0ULL;
        writeOffset = 0ULL;
        failed = FALSE;
        ok = ProbeInit1("_S32_Attempt.ptrT", (uint64_t)8U, Dest);
        if (ok)
        {
          S32attemptProbePtrTT("_S32_Attempt",
            "ptrT",
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
          ErrorHandlerFn("_S32_Attempt",
            "ptrT",
            "probe",
            0ULL,
            Ctxt,
            EverParseStreamOf(Dest),
            0ULL);
          b = 0ULL;
        }
        else
        {
          b = wr;
        }
        if (b != 0ULL)
        {
          result =
            ValidateT(f,
              Ctxt,
              ErrorHandlerFn,
              EverParseStreamOf(Dest),
              EverParseStreamLen(Dest),
              0ULL);
          actionResult = !EverParseIsError(result);
        }
        else
        {
          ErrorHandlerFn("_S32_Attempt",
            "ptrT",
            EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
            EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
            Ctxt,
            Input,
            positionAfterCheckedF);
          actionResult = FALSE;
        }
        if (actionResult)
        {
          positionAfterPtrT1 = positionAfterPtrT0;
        }
        else
        {
          positionAfterPtrT1 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
              positionAfterPtrT0);
        }
      }
      if (EverParseIsSuccess(positionAfterPtrT1))
      {
        positionAfterPtrT = positionAfterPtrT1;
      }
      else
      {
        ErrorHandlerFn("_S32_Attempt",
          "ptrT",
          EverParseErrorReasonOfResult(positionAfterPtrT1),
          EverParseGetValidatorErrorKind(positionAfterPtrT1),
          Ctxt,
          Input,
          positionAfterCheckedF);
        positionAfterPtrT = positionAfterPtrT1;
      }
      if (EverParseIsError(positionAfterPtrT))
      {
        positionAfterF = positionAfterPtrT;
      }
      else
      {
        /* Validating field g */
        /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
        hasBytesForG = (InputLength - positionAfterPtrT) >= 4ULL;
        if (hasBytesForG)
        {
          positionAfterG = positionAfterPtrT + 4ULL;
        }
        else
        {
          positionAfterG =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAfterPtrT);
        }
        if (EverParseIsSuccess(positionAfterG))
        {
          res = positionAfterG;
        }
        else
        {
          ErrorHandlerFn("_S32_Attempt",
            "g",
            EverParseErrorReasonOfResult(positionAfterG),
            EverParseGetValidatorErrorKind(positionAfterG),
            Ctxt,
            Input,
            positionAfterPtrT);
          res = positionAfterG;
        }
        positionAfterF = res;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterF))
  {
    return positionAfterF;
  }
  ErrorHandlerFn("_S32_Attempt",
    "f",
    EverParseErrorReasonOfResult(positionAfterF),
    EverParseGetValidatorErrorKind(positionAfterF),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterF;
}

static void
R32AttemptProbePtrSS32attempt(
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
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
  uint64_t res1 = Sz;
  BOOLEAN hasFailed = *Failed;
  uint64_t rd;
  uint64_t wr;
  BOOLEAN ok;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  rd = *ReadOffset;
  wr = *WriteOffset;
  ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

static inline uint64_t
ValidateR32Attempt(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytesForF = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterF0;
  uint64_t positionAfterF;
  uint32_t f;
  BOOLEAN hasBytesForPtrS;
  uint64_t positionAfterPtrS0;
  uint64_t positionAfterPtrS;
  uint32_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint64_t result;
  if (hasBytesForF)
  {
    positionAfterF0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterF0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterF0))
  {
    positionAfterF = positionAfterF0;
  }
  else
  {
    ErrorHandlerFn("_R32_Attempt",
      "f",
      EverParseErrorReasonOfResult(positionAfterF0),
      EverParseGetValidatorErrorKind(positionAfterF0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterF = positionAfterF0;
  }
  if (EverParseIsError(positionAfterF))
  {
    return positionAfterF;
  }
  f = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytesForPtrS = (InputLength - positionAfterF) >= 4ULL;
  if (hasBytesForPtrS)
  {
    positionAfterPtrS0 = positionAfterF + 4ULL;
  }
  else
  {
    positionAfterPtrS0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterF);
  }
  if (EverParseIsError(positionAfterPtrS0))
  {
    positionAfterPtrS = positionAfterPtrS0;
  }
  else
  {
    ptrS = Load32Le(Input + (uint32_t)positionAfterF);
    src64 = UlongToPtr1(ptrS);
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    ok = ProbeInit1("_R32_Attempt.ptrS", (uint64_t)12U, DestS);
    if (ok)
    {
      R32AttemptProbePtrSS32attempt("_R32_Attempt",
        "ptrS",
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
      ErrorHandlerFn("_R32_Attempt", "ptrS", "probe", 0ULL, Ctxt, EverParseStreamOf(DestS), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    if (b != 0ULL)
    {
      result =
        ValidateS32Attempt(f,
          DestT,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestS),
          EverParseStreamLen(DestS),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_R32_Attempt",
        "ptrS",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAfterF);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterPtrS = positionAfterPtrS0;
    }
    else
    {
      positionAfterPtrS =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtrS0);
    }
  }
  if (EverParseIsSuccess(positionAfterPtrS))
  {
    return positionAfterPtrS;
  }
  ErrorHandlerFn("_R32_Attempt",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterPtrS),
    EverParseGetValidatorErrorKind(positionAfterPtrS),
    Ctxt,
    Input,
    positionAfterF);
  return positionAfterPtrS;
}

static void
RmuxProbeFieldR640T(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
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
  KRML_MAYBE_UNUSED_VAR(Det);
  res1 = Sz;
  hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  rd = *ReadOffset;
  wr = *WriteOffset;
  ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

static void
RmuxProbeFieldR641S64(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
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
  KRML_MAYBE_UNUSED_VAR(Det);
  res1 = Sz;
  hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  rd = *ReadOffset;
  wr = *WriteOffset;
  ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

uint64_t
Specialize1ValidateRmux(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  uint64_t positionAfterR32;
  uint64_t positionAfterR64;
  if (Requestor32)
  {
    /* Validating field r32 */
    positionAfterR32 =
      ValidateR32Attempt(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterR32))
    {
      return positionAfterR32;
    }
    ErrorHandlerFn("_RMux",
      "r32",
      EverParseErrorReasonOfResult(positionAfterR32),
      EverParseGetValidatorErrorKind(positionAfterR32),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterR32;
  }
  /* Validating field r64 */
  positionAfterR64 =
    ValidateR64(RmuxProbeFieldR640T,
      RmuxProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterR64))
  {
    return positionAfterR64;
  }
  ErrorHandlerFn("_RMux",
    "r64",
    EverParseErrorReasonOfResult(positionAfterR64),
    EverParseGetValidatorErrorKind(positionAfterR64),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterR64;
}

