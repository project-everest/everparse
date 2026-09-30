

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
  uint64_t positionAfterT1OrError;
  uint64_t resForT1;
  uint64_t positionAfterT1;
  BOOLEAN hasBytesForT2_refinement;
  uint64_t positionAfterT2_refinement;
  uint64_t positionAfterT2_refinementOrError;
  uint32_t t2_refinement;
  BOOLEAN t2_refinementConstraintIsOk;
  if (hasBytesForT1)
  {
    positionAfterT1OrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterT1OrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterT1OrError))
  {
    resForT1 = positionAfterT1OrError;
  }
  else
  {
    ErrorHandlerFn("_T",
      "t1",
      EverParseErrorReasonOfResult(positionAfterT1OrError),
      EverParseGetValidatorErrorKind(positionAfterT1OrError),
      Ctxt,
      Input,
      StartPosition);
    resForT1 = positionAfterT1OrError;
  }
  positionAfterT1 = resForT1;
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
    positionAfterT2_refinementOrError = positionAfterT2_refinement;
  }
  else
  {
    /* reading field_value */
    t2_refinement = Load32Le(Input + (uint32_t)positionAfterT1);
    /* start: checking constraint */
    t2_refinementConstraintIsOk = t2_refinement <= Bound;
    /* end: checking constraint */
    positionAfterT2_refinementOrError =
      EverParseCheckConstraintOk(t2_refinementConstraintIsOk,
        positionAfterT2_refinement);
  }
  if (EverParseIsSuccess(positionAfterT2_refinementOrError))
  {
    return positionAfterT2_refinementOrError;
  }
  ErrorHandlerFn("_T",
    "t2.refinement",
    EverParseErrorReasonOfResult(positionAfterT2_refinementOrError),
    EverParseGetValidatorErrorKind(positionAfterT2_refinementOrError),
    Ctxt,
    Input,
    positionAfterT1);
  return positionAfterT2_refinementOrError;
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
  uint64_t positionAfterS1;
  uint64_t positionAfterS1OrError;
  uint32_t s1;
  BOOLEAN s1ConstraintIsOk;
  uint64_t positionAfterCheckedS1;
  BOOLEAN hasBytesForAlignmentPadding4;
  uint64_t resForAlignmentPadding4;
  uint64_t positionAfterAlignmentPadding4orError;
  uint64_t positionAfterAlignmentPadding4;
  BOOLEAN hasBytesForPtrT;
  uint64_t positionAfterPtrT0;
  uint64_t positionAfterPtrTOrError;
  uint64_t ptrT;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForPtrT;
  uint64_t wr;
  BOOLEAN hasFailedForPtrT;
  uint64_t b;
  BOOLEAN actionResultForPtrT;
  uint64_t result;
  uint64_t positionAfterPtrT;
  BOOLEAN hasBytesForS2;
  uint64_t resForS2;
  uint64_t positionAfterS2OrError;
  if (hasBytesForS1)
  {
    positionAfterS1 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterS1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterS1))
  {
    positionAfterS1OrError = positionAfterS1;
  }
  else
  {
    s1 = Load32Le(Input + (uint32_t)StartPosition);
    s1ConstraintIsOk = s1 <= Bound;
    positionAfterCheckedS1 = EverParseCheckConstraintOk(s1ConstraintIsOk, positionAfterS1);
    if (EverParseIsError(positionAfterCheckedS1))
    {
      positionAfterS1OrError = positionAfterCheckedS1;
    }
    else
    {
      /* Validating field ___alignment_padding_4 */
      hasBytesForAlignmentPadding4 = (InputLength - positionAfterCheckedS1) >= (uint64_t)4U;
      if (hasBytesForAlignmentPadding4)
      {
        resForAlignmentPadding4 = positionAfterCheckedS1 + (uint64_t)4U;
      }
      else
      {
        resForAlignmentPadding4 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedS1);
      }
      positionAfterAlignmentPadding4orError = resForAlignmentPadding4;
      if (EverParseIsSuccess(positionAfterAlignmentPadding4orError))
      {
        positionAfterAlignmentPadding4 = positionAfterAlignmentPadding4orError;
      }
      else
      {
        ErrorHandlerFn("_S64",
          "___alignment_padding_4",
          EverParseErrorReasonOfResult(positionAfterAlignmentPadding4orError),
          EverParseGetValidatorErrorKind(positionAfterAlignmentPadding4orError),
          Ctxt,
          Input,
          positionAfterCheckedS1);
        positionAfterAlignmentPadding4 = positionAfterAlignmentPadding4orError;
      }
      if (EverParseIsError(positionAfterAlignmentPadding4))
      {
        positionAfterS1OrError = positionAfterAlignmentPadding4;
      }
      else
      {
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        hasBytesForPtrT = (InputLength - positionAfterAlignmentPadding4) >= 8ULL;
        if (hasBytesForPtrT)
        {
          positionAfterPtrT0 = positionAfterAlignmentPadding4 + 8ULL;
        }
        else
        {
          positionAfterPtrT0 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAfterAlignmentPadding4);
        }
        if (EverParseIsError(positionAfterPtrT0))
        {
          positionAfterPtrTOrError = positionAfterPtrT0;
        }
        else
        {
          ptrT = Load64Le(Input + (uint32_t)positionAfterAlignmentPadding4);
          src64 = ptrT;
          readOffset = 0ULL;
          writeOffset = 0ULL;
          failed = FALSE;
          okForPtrT = ProbeInit1("_S64.ptrT", (uint64_t)8U, Dest);
          if (okForPtrT)
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
          hasFailedForPtrT = failed;
          if (hasFailedForPtrT)
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
            actionResultForPtrT = !EverParseIsError(result);
          }
          else
          {
            ErrorHandlerFn("_S64",
              "ptrT",
              EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
              EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
              Ctxt,
              Input,
              positionAfterAlignmentPadding4);
            actionResultForPtrT = FALSE;
          }
          if (actionResultForPtrT)
          {
            positionAfterPtrTOrError = positionAfterPtrT0;
          }
          else
          {
            positionAfterPtrTOrError =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
                positionAfterPtrT0);
          }
        }
        if (EverParseIsSuccess(positionAfterPtrTOrError))
        {
          positionAfterPtrT = positionAfterPtrTOrError;
        }
        else
        {
          ErrorHandlerFn("_S64",
            "ptrT",
            EverParseErrorReasonOfResult(positionAfterPtrTOrError),
            EverParseGetValidatorErrorKind(positionAfterPtrTOrError),
            Ctxt,
            Input,
            positionAfterAlignmentPadding4);
          positionAfterPtrT = positionAfterPtrTOrError;
        }
        if (EverParseIsError(positionAfterPtrT))
        {
          positionAfterS1OrError = positionAfterPtrT;
        }
        else
        {
          hasBytesForS2 = (InputLength - positionAfterPtrT) >= 8ULL;
          if (hasBytesForS2)
          {
            resForS2 = positionAfterPtrT + 8ULL;
          }
          else
          {
            resForS2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterPtrT);
          }
          positionAfterS2OrError = resForS2;
          if (EverParseIsSuccess(positionAfterS2OrError))
          {
            positionAfterS1OrError = positionAfterS2OrError;
          }
          else
          {
            ErrorHandlerFn("_S64",
              "s2",
              EverParseErrorReasonOfResult(positionAfterS2OrError),
              EverParseGetValidatorErrorKind(positionAfterS2OrError),
              Ctxt,
              Input,
              positionAfterPtrT);
            positionAfterS1OrError = positionAfterS2OrError;
          }
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfterS1OrError))
  {
    return positionAfterS1OrError;
  }
  ErrorHandlerFn("_S64",
    "s1",
    EverParseErrorReasonOfResult(positionAfterS1OrError),
    EverParseGetValidatorErrorKind(positionAfterS1OrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterS1OrError;
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
  uint64_t positionAfterR1OrError;
  uint64_t positionAfterR1;
  uint32_t r1;
  BOOLEAN hasBytesForAlignmentPadding6;
  uint64_t resForAlignmentPadding6;
  uint64_t positionAfterAlignmentPadding6orError;
  uint64_t positionAfterAlignmentPadding6;
  BOOLEAN hasBytesForPtrS;
  uint64_t positionAfterPtrS;
  uint64_t positionAfterPtrSOrError;
  uint64_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForPtrS;
  uint64_t wr;
  BOOLEAN hasFailedForPtrS;
  uint64_t b;
  BOOLEAN actionResultForPtrS;
  uint64_t result;
  if (hasBytesForR1)
  {
    positionAfterR1OrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterR1OrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterR1OrError))
  {
    positionAfterR1 = positionAfterR1OrError;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "r1",
      EverParseErrorReasonOfResult(positionAfterR1OrError),
      EverParseGetValidatorErrorKind(positionAfterR1OrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterR1 = positionAfterR1OrError;
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
    resForAlignmentPadding6 = positionAfterR1 + (uint64_t)4U;
  }
  else
  {
    resForAlignmentPadding6 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterR1);
  }
  positionAfterAlignmentPadding6orError = resForAlignmentPadding6;
  if (EverParseIsSuccess(positionAfterAlignmentPadding6orError))
  {
    positionAfterAlignmentPadding6 = positionAfterAlignmentPadding6orError;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "___alignment_padding_6",
      EverParseErrorReasonOfResult(positionAfterAlignmentPadding6orError),
      EverParseGetValidatorErrorKind(positionAfterAlignmentPadding6orError),
      Ctxt,
      Input,
      positionAfterR1);
    positionAfterAlignmentPadding6 = positionAfterAlignmentPadding6orError;
  }
  if (EverParseIsError(positionAfterAlignmentPadding6))
  {
    return positionAfterAlignmentPadding6;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForPtrS = (InputLength - positionAfterAlignmentPadding6) >= 8ULL;
  if (hasBytesForPtrS)
  {
    positionAfterPtrS = positionAfterAlignmentPadding6 + 8ULL;
  }
  else
  {
    positionAfterPtrS =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterAlignmentPadding6);
  }
  if (EverParseIsError(positionAfterPtrS))
  {
    positionAfterPtrSOrError = positionAfterPtrS;
  }
  else
  {
    ptrS = Load64Le(Input + (uint32_t)positionAfterAlignmentPadding6);
    src64 = ptrS;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    okForPtrS = ProbeInit1("_R64.ptrS", (uint64_t)24U, DestS);
    if (okForPtrS)
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
    hasFailedForPtrS = failed;
    if (hasFailedForPtrS)
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
      actionResultForPtrS = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_R64",
        "ptrS",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAfterAlignmentPadding6);
      actionResultForPtrS = FALSE;
    }
    if (actionResultForPtrS)
    {
      positionAfterPtrSOrError = positionAfterPtrS;
    }
    else
    {
      positionAfterPtrSOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtrS);
    }
  }
  if (EverParseIsSuccess(positionAfterPtrSOrError))
  {
    return positionAfterPtrSOrError;
  }
  ErrorHandlerFn("_R64",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterPtrSOrError),
    EverParseGetValidatorErrorKind(positionAfterPtrSOrError),
    Ctxt,
    Input,
    positionAfterAlignmentPadding6);
  return positionAfterPtrSOrError;
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
  uint64_t positionAfterR1OrError;
  uint64_t positionAfterR1;
  uint32_t r1;
  BOOLEAN hasBytesForPtrS;
  uint64_t positionAfterPtrS;
  uint64_t positionAfterPtrSOrError;
  uint32_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForPtrS;
  uint64_t wr;
  BOOLEAN hasFailedForPtrS;
  uint64_t b;
  BOOLEAN actionResultForPtrS;
  uint64_t result;
  if (hasBytesForR1)
  {
    positionAfterR1OrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterR1OrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterR1OrError))
  {
    positionAfterR1 = positionAfterR1OrError;
  }
  else
  {
    ErrorHandlerFn("___specialized_R32",
      "r1",
      EverParseErrorReasonOfResult(positionAfterR1OrError),
      EverParseGetValidatorErrorKind(positionAfterR1OrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterR1 = positionAfterR1OrError;
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
    positionAfterPtrS = positionAfterR1 + 4ULL;
  }
  else
  {
    positionAfterPtrS =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterR1);
  }
  if (EverParseIsError(positionAfterPtrS))
  {
    positionAfterPtrSOrError = positionAfterPtrS;
  }
  else
  {
    ptrS = Load32Le(Input + (uint32_t)positionAfterR1);
    src64 = UlongToPtr1(ptrS);
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    okForPtrS = ProbeInit1("___specialized_R32.ptrS", (uint64_t)24U, DestS);
    if (okForPtrS)
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
    hasFailedForPtrS = failed;
    if (hasFailedForPtrS)
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
      actionResultForPtrS = !EverParseIsError(result);
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
      actionResultForPtrS = FALSE;
    }
    if (actionResultForPtrS)
    {
      positionAfterPtrSOrError = positionAfterPtrS;
    }
    else
    {
      positionAfterPtrSOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtrS);
    }
  }
  if (EverParseIsSuccess(positionAfterPtrSOrError))
  {
    return positionAfterPtrSOrError;
  }
  ErrorHandlerFn("___specialized_R32",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterPtrSOrError),
    EverParseGetValidatorErrorKind(positionAfterPtrSOrError),
    Ctxt,
    Input,
    positionAfterR1);
  return positionAfterPtrSOrError;
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
  uint64_t positionAfterR32OrError;
  uint64_t positionAfterR64OrError;
  if (Requestor32)
  {
    /* Validating field r32 */
    positionAfterR32OrError =
      ValidateSpecializedR32(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterR32OrError))
    {
      return positionAfterR32OrError;
    }
    ErrorHandlerFn("___R",
      "r32",
      EverParseErrorReasonOfResult(positionAfterR32OrError),
      EverParseGetValidatorErrorKind(positionAfterR32OrError),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterR32OrError;
  }
  /* Validating field r64 */
  positionAfterR64OrError =
    ValidateR64(RProbeFieldR640T,
      RProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterR64OrError))
  {
    return positionAfterR64OrError;
  }
  ErrorHandlerFn("___R",
    "r64",
    EverParseErrorReasonOfResult(positionAfterR64OrError),
    EverParseGetValidatorErrorKind(positionAfterR64OrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterR64OrError;
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
  uint64_t positionAfterF;
  uint64_t positionAfterFOrError;
  uint32_t f;
  BOOLEAN fConstraintIsOk;
  uint64_t positionAfterCheckedF;
  BOOLEAN hasBytesForPtrT;
  uint64_t positionAfterPtrT0;
  uint64_t positionAfterPtrTOrError;
  uint32_t ptrT;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForPtrT;
  uint64_t wr;
  BOOLEAN hasFailedForPtrT;
  uint64_t b;
  BOOLEAN actionResultForPtrT;
  uint64_t result;
  uint64_t positionAfterPtrT;
  BOOLEAN hasBytesForG;
  uint64_t positionAfterGOrError;
  uint64_t resForG;
  if (hasBytesForF)
  {
    positionAfterF = StartPosition + 4ULL;
  }
  else
  {
    positionAfterF =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterF))
  {
    positionAfterFOrError = positionAfterF;
  }
  else
  {
    f = Load32Le(Input + (uint32_t)StartPosition);
    fConstraintIsOk = f <= Bound;
    positionAfterCheckedF = EverParseCheckConstraintOk(fConstraintIsOk, positionAfterF);
    if (EverParseIsError(positionAfterCheckedF))
    {
      positionAfterFOrError = positionAfterCheckedF;
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
        positionAfterPtrTOrError = positionAfterPtrT0;
      }
      else
      {
        ptrT = Load32Le(Input + (uint32_t)positionAfterCheckedF);
        src64 = UlongToPtr1(ptrT);
        readOffset = 0ULL;
        writeOffset = 0ULL;
        failed = FALSE;
        okForPtrT = ProbeInit1("_S32_Attempt.ptrT", (uint64_t)8U, Dest);
        if (okForPtrT)
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
        hasFailedForPtrT = failed;
        if (hasFailedForPtrT)
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
          actionResultForPtrT = !EverParseIsError(result);
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
          actionResultForPtrT = FALSE;
        }
        if (actionResultForPtrT)
        {
          positionAfterPtrTOrError = positionAfterPtrT0;
        }
        else
        {
          positionAfterPtrTOrError =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
              positionAfterPtrT0);
        }
      }
      if (EverParseIsSuccess(positionAfterPtrTOrError))
      {
        positionAfterPtrT = positionAfterPtrTOrError;
      }
      else
      {
        ErrorHandlerFn("_S32_Attempt",
          "ptrT",
          EverParseErrorReasonOfResult(positionAfterPtrTOrError),
          EverParseGetValidatorErrorKind(positionAfterPtrTOrError),
          Ctxt,
          Input,
          positionAfterCheckedF);
        positionAfterPtrT = positionAfterPtrTOrError;
      }
      if (EverParseIsError(positionAfterPtrT))
      {
        positionAfterFOrError = positionAfterPtrT;
      }
      else
      {
        /* Validating field g */
        /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
        hasBytesForG = (InputLength - positionAfterPtrT) >= 4ULL;
        if (hasBytesForG)
        {
          positionAfterGOrError = positionAfterPtrT + 4ULL;
        }
        else
        {
          positionAfterGOrError =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAfterPtrT);
        }
        if (EverParseIsSuccess(positionAfterGOrError))
        {
          resForG = positionAfterGOrError;
        }
        else
        {
          ErrorHandlerFn("_S32_Attempt",
            "g",
            EverParseErrorReasonOfResult(positionAfterGOrError),
            EverParseGetValidatorErrorKind(positionAfterGOrError),
            Ctxt,
            Input,
            positionAfterPtrT);
          resForG = positionAfterGOrError;
        }
        positionAfterFOrError = resForG;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterFOrError))
  {
    return positionAfterFOrError;
  }
  ErrorHandlerFn("_S32_Attempt",
    "f",
    EverParseErrorReasonOfResult(positionAfterFOrError),
    EverParseGetValidatorErrorKind(positionAfterFOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterFOrError;
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
  uint64_t positionAfterFOrError;
  uint64_t positionAfterF;
  uint32_t f;
  BOOLEAN hasBytesForPtrS;
  uint64_t positionAfterPtrS;
  uint64_t positionAfterPtrSOrError;
  uint32_t ptrS;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForPtrS;
  uint64_t wr;
  BOOLEAN hasFailedForPtrS;
  uint64_t b;
  BOOLEAN actionResultForPtrS;
  uint64_t result;
  if (hasBytesForF)
  {
    positionAfterFOrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterFOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterFOrError))
  {
    positionAfterF = positionAfterFOrError;
  }
  else
  {
    ErrorHandlerFn("_R32_Attempt",
      "f",
      EverParseErrorReasonOfResult(positionAfterFOrError),
      EverParseGetValidatorErrorKind(positionAfterFOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterF = positionAfterFOrError;
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
    positionAfterPtrS = positionAfterF + 4ULL;
  }
  else
  {
    positionAfterPtrS =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterF);
  }
  if (EverParseIsError(positionAfterPtrS))
  {
    positionAfterPtrSOrError = positionAfterPtrS;
  }
  else
  {
    ptrS = Load32Le(Input + (uint32_t)positionAfterF);
    src64 = UlongToPtr1(ptrS);
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    okForPtrS = ProbeInit1("_R32_Attempt.ptrS", (uint64_t)12U, DestS);
    if (okForPtrS)
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
    hasFailedForPtrS = failed;
    if (hasFailedForPtrS)
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
      actionResultForPtrS = !EverParseIsError(result);
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
      actionResultForPtrS = FALSE;
    }
    if (actionResultForPtrS)
    {
      positionAfterPtrSOrError = positionAfterPtrS;
    }
    else
    {
      positionAfterPtrSOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtrS);
    }
  }
  if (EverParseIsSuccess(positionAfterPtrSOrError))
  {
    return positionAfterPtrSOrError;
  }
  ErrorHandlerFn("_R32_Attempt",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterPtrSOrError),
    EverParseGetValidatorErrorKind(positionAfterPtrSOrError),
    Ctxt,
    Input,
    positionAfterF);
  return positionAfterPtrSOrError;
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
  uint64_t positionAfterR32OrError;
  uint64_t positionAfterR64OrError;
  if (Requestor32)
  {
    /* Validating field r32 */
    positionAfterR32OrError =
      ValidateR32Attempt(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterR32OrError))
    {
      return positionAfterR32OrError;
    }
    ErrorHandlerFn("_RMux",
      "r32",
      EverParseErrorReasonOfResult(positionAfterR32OrError),
      EverParseGetValidatorErrorKind(positionAfterR32OrError),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterR32OrError;
  }
  /* Validating field r64 */
  positionAfterR64OrError =
    ValidateR64(RmuxProbeFieldR640T,
      RmuxProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterR64OrError))
  {
    return positionAfterR64OrError;
  }
  ErrorHandlerFn("_RMux",
    "r64",
    EverParseErrorReasonOfResult(positionAfterR64OrError),
    EverParseGetValidatorErrorKind(positionAfterR64OrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterR64OrError;
}

