

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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAftert10;
  uint64_t res;
  uint64_t positionAftert1;
  BOOLEAN hasBytes;
  uint64_t positionAftert2_refinement;
  uint64_t positionAftert2_refinement0;
  uint32_t t2_refinement;
  BOOLEAN t2_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAftert10 = StartPosition + 4ULL;
  }
  else
  {
    positionAftert10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAftert10))
  {
    res = positionAftert10;
  }
  else
  {
    ErrorHandlerFn("_T",
      "t1",
      EverParseErrorReasonOfResult(positionAftert10),
      EverParseGetValidatorErrorKind(positionAftert10),
      Ctxt,
      Input,
      StartPosition);
    res = positionAftert10;
  }
  positionAftert1 = res;
  if (EverParseIsError(positionAftert1))
  {
    return positionAftert1;
  }
  /* Validating field t2 */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAftert1) >= 4ULL;
  if (hasBytes)
  {
    positionAftert2_refinement = positionAftert1 + 4ULL;
  }
  else
  {
    positionAftert2_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftert1);
  }
  if (EverParseIsError(positionAftert2_refinement))
  {
    positionAftert2_refinement0 = positionAftert2_refinement;
  }
  else
  {
    /* reading field_value */
    t2_refinement = Load32Le(Input + (uint32_t)positionAftert1);
    /* start: checking constraint */
    t2_refinementConstraintIsOk = t2_refinement <= Bound;
    /* end: checking constraint */
    positionAftert2_refinement0 =
      EverParseCheckConstraintOk(t2_refinementConstraintIsOk,
        positionAftert2_refinement);
  }
  if (EverParseIsSuccess(positionAftert2_refinement0))
  {
    return positionAftert2_refinement0;
  }
  ErrorHandlerFn("_T",
    "t2.refinement",
    EverParseErrorReasonOfResult(positionAftert2_refinement0),
    EverParseGetValidatorErrorKind(positionAftert2_refinement0),
    Ctxt,
    Input,
    positionAftert1);
  return positionAftert2_refinement0;
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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfters10;
  uint64_t positionAfters1;
  uint32_t s1;
  BOOLEAN s1ConstraintIsOk;
  uint64_t positionAfterCheckeds1;
  BOOLEAN hasBytes1;
  uint64_t res0;
  uint64_t positionAfterAlignmentPadding4;
  uint64_t positionAfterAlignmentPadding40;
  BOOLEAN hasBytes2;
  uint64_t positionAfterptrT0;
  uint64_t positionAfterptrT1;
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
  uint64_t positionAfterptrT;
  BOOLEAN hasBytes;
  uint64_t res;
  uint64_t positionAfters2;
  if (hasBytes0)
  {
    positionAfters10 = StartPosition + 4ULL;
  }
  else
  {
    positionAfters10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfters10))
  {
    positionAfters1 = positionAfters10;
  }
  else
  {
    s1 = Load32Le(Input + (uint32_t)StartPosition);
    s1ConstraintIsOk = s1 <= Bound;
    positionAfterCheckeds1 = EverParseCheckConstraintOk(s1ConstraintIsOk, positionAfters10);
    if (EverParseIsError(positionAfterCheckeds1))
    {
      positionAfters1 = positionAfterCheckeds1;
    }
    else
    {
      /* Validating field ___alignment_padding_4 */
      hasBytes1 = (InputLength - positionAfterCheckeds1) >= (uint64_t)4U;
      if (hasBytes1)
      {
        res0 = positionAfterCheckeds1 + (uint64_t)4U;
      }
      else
      {
        res0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckeds1);
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
          positionAfterCheckeds1);
        positionAfterAlignmentPadding40 = positionAfterAlignmentPadding4;
      }
      if (EverParseIsError(positionAfterAlignmentPadding40))
      {
        positionAfters1 = positionAfterAlignmentPadding40;
      }
      else
      {
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        hasBytes2 = (InputLength - positionAfterAlignmentPadding40) >= 8ULL;
        if (hasBytes2)
        {
          positionAfterptrT0 = positionAfterAlignmentPadding40 + 8ULL;
        }
        else
        {
          positionAfterptrT0 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAfterAlignmentPadding40);
        }
        if (EverParseIsError(positionAfterptrT0))
        {
          positionAfterptrT1 = positionAfterptrT0;
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
            positionAfterptrT1 = positionAfterptrT0;
          }
          else
          {
            positionAfterptrT1 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
                positionAfterptrT0);
          }
        }
        if (EverParseIsSuccess(positionAfterptrT1))
        {
          positionAfterptrT = positionAfterptrT1;
        }
        else
        {
          ErrorHandlerFn("_S64",
            "ptrT",
            EverParseErrorReasonOfResult(positionAfterptrT1),
            EverParseGetValidatorErrorKind(positionAfterptrT1),
            Ctxt,
            Input,
            positionAfterAlignmentPadding40);
          positionAfterptrT = positionAfterptrT1;
        }
        if (EverParseIsError(positionAfterptrT))
        {
          positionAfters1 = positionAfterptrT;
        }
        else
        {
          hasBytes = (InputLength - positionAfterptrT) >= 8ULL;
          if (hasBytes)
          {
            res = positionAfterptrT + 8ULL;
          }
          else
          {
            res =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterptrT);
          }
          positionAfters2 = res;
          if (EverParseIsSuccess(positionAfters2))
          {
            positionAfters1 = positionAfters2;
          }
          else
          {
            ErrorHandlerFn("_S64",
              "s2",
              EverParseErrorReasonOfResult(positionAfters2),
              EverParseGetValidatorErrorKind(positionAfters2),
              Ctxt,
              Input,
              positionAfterptrT);
            positionAfters1 = positionAfters2;
          }
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfters1))
  {
    return positionAfters1;
  }
  ErrorHandlerFn("_S64",
    "s1",
    EverParseErrorReasonOfResult(positionAfters1),
    EverParseGetValidatorErrorKind(positionAfters1),
    Ctxt,
    Input,
    StartPosition);
  return positionAfters1;
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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterr10;
  uint64_t positionAfterr1;
  uint32_t r1;
  BOOLEAN hasBytes1;
  uint64_t res;
  uint64_t positionAfterAlignmentPadding6;
  uint64_t positionAfterAlignmentPadding60;
  BOOLEAN hasBytes;
  uint64_t positionAfterptrS0;
  uint64_t positionAfterptrS;
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
  if (hasBytes0)
  {
    positionAfterr10 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterr10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterr10))
  {
    positionAfterr1 = positionAfterr10;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "r1",
      EverParseErrorReasonOfResult(positionAfterr10),
      EverParseGetValidatorErrorKind(positionAfterr10),
      Ctxt,
      Input,
      StartPosition);
    positionAfterr1 = positionAfterr10;
  }
  if (EverParseIsError(positionAfterr1))
  {
    return positionAfterr1;
  }
  r1 = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field ___alignment_padding_6 */
  hasBytes1 = (InputLength - positionAfterr1) >= (uint64_t)4U;
  if (hasBytes1)
  {
    res = positionAfterr1 + (uint64_t)4U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, positionAfterr1);
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
      positionAfterr1);
    positionAfterAlignmentPadding60 = positionAfterAlignmentPadding6;
  }
  if (EverParseIsError(positionAfterAlignmentPadding60))
  {
    return positionAfterAlignmentPadding60;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = (InputLength - positionAfterAlignmentPadding60) >= 8ULL;
  if (hasBytes)
  {
    positionAfterptrS0 = positionAfterAlignmentPadding60 + 8ULL;
  }
  else
  {
    positionAfterptrS0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterAlignmentPadding60);
  }
  if (EverParseIsError(positionAfterptrS0))
  {
    positionAfterptrS = positionAfterptrS0;
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
      positionAfterptrS = positionAfterptrS0;
    }
    else
    {
      positionAfterptrS =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptrS0);
    }
  }
  if (EverParseIsSuccess(positionAfterptrS))
  {
    return positionAfterptrS;
  }
  ErrorHandlerFn("_R64",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterptrS),
    EverParseGetValidatorErrorKind(positionAfterptrS),
    Ctxt,
    Input,
    positionAfterAlignmentPadding60);
  return positionAfterptrS;
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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterr10;
  uint64_t positionAfterr1;
  uint32_t r1;
  BOOLEAN hasBytes;
  uint64_t positionAfterptrS0;
  uint64_t positionAfterptrS;
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
  if (hasBytes0)
  {
    positionAfterr10 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterr10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterr10))
  {
    positionAfterr1 = positionAfterr10;
  }
  else
  {
    ErrorHandlerFn("___specialized_R32",
      "r1",
      EverParseErrorReasonOfResult(positionAfterr10),
      EverParseGetValidatorErrorKind(positionAfterr10),
      Ctxt,
      Input,
      StartPosition);
    positionAfterr1 = positionAfterr10;
  }
  if (EverParseIsError(positionAfterr1))
  {
    return positionAfterr1;
  }
  r1 = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterr1) >= 4ULL;
  if (hasBytes)
  {
    positionAfterptrS0 = positionAfterr1 + 4ULL;
  }
  else
  {
    positionAfterptrS0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterr1);
  }
  if (EverParseIsError(positionAfterptrS0))
  {
    positionAfterptrS = positionAfterptrS0;
  }
  else
  {
    ptrS = Load32Le(Input + (uint32_t)positionAfterr1);
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
        positionAfterr1);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterptrS = positionAfterptrS0;
    }
    else
    {
      positionAfterptrS =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptrS0);
    }
  }
  if (EverParseIsSuccess(positionAfterptrS))
  {
    return positionAfterptrS;
  }
  ErrorHandlerFn("___specialized_R32",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterptrS),
    EverParseGetValidatorErrorKind(positionAfterptrS),
    Ctxt,
    Input,
    positionAfterr1);
  return positionAfterptrS;
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
  uint64_t positionAfterr32;
  uint64_t positionAfterr64;
  if (Requestor32)
  {
    /* Validating field r32 */
    positionAfterr32 =
      ValidateSpecializedR32(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterr32))
    {
      return positionAfterr32;
    }
    ErrorHandlerFn("___R",
      "r32",
      EverParseErrorReasonOfResult(positionAfterr32),
      EverParseGetValidatorErrorKind(positionAfterr32),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterr32;
  }
  /* Validating field r64 */
  positionAfterr64 =
    ValidateR64(RProbeFieldR640T,
      RProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterr64))
  {
    return positionAfterr64;
  }
  ErrorHandlerFn("___R",
    "r64",
    EverParseErrorReasonOfResult(positionAfterr64),
    EverParseGetValidatorErrorKind(positionAfterr64),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterr64;
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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterf0;
  uint64_t positionAfterf;
  uint32_t f;
  BOOLEAN fConstraintIsOk;
  uint64_t positionAfterCheckedf;
  BOOLEAN hasBytes1;
  uint64_t positionAfterptrT0;
  uint64_t positionAfterptrT1;
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
  uint64_t positionAfterptrT;
  BOOLEAN hasBytes;
  uint64_t positionAfterg;
  uint64_t res;
  if (hasBytes0)
  {
    positionAfterf0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterf0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterf0))
  {
    positionAfterf = positionAfterf0;
  }
  else
  {
    f = Load32Le(Input + (uint32_t)StartPosition);
    fConstraintIsOk = f <= Bound;
    positionAfterCheckedf = EverParseCheckConstraintOk(fConstraintIsOk, positionAfterf0);
    if (EverParseIsError(positionAfterCheckedf))
    {
      positionAfterf = positionAfterCheckedf;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      hasBytes1 = (InputLength - positionAfterCheckedf) >= 4ULL;
      if (hasBytes1)
      {
        positionAfterptrT0 = positionAfterCheckedf + 4ULL;
      }
      else
      {
        positionAfterptrT0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedf);
      }
      if (EverParseIsError(positionAfterptrT0))
      {
        positionAfterptrT1 = positionAfterptrT0;
      }
      else
      {
        ptrT = Load32Le(Input + (uint32_t)positionAfterCheckedf);
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
            positionAfterCheckedf);
          actionResult = FALSE;
        }
        if (actionResult)
        {
          positionAfterptrT1 = positionAfterptrT0;
        }
        else
        {
          positionAfterptrT1 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
              positionAfterptrT0);
        }
      }
      if (EverParseIsSuccess(positionAfterptrT1))
      {
        positionAfterptrT = positionAfterptrT1;
      }
      else
      {
        ErrorHandlerFn("_S32_Attempt",
          "ptrT",
          EverParseErrorReasonOfResult(positionAfterptrT1),
          EverParseGetValidatorErrorKind(positionAfterptrT1),
          Ctxt,
          Input,
          positionAfterCheckedf);
        positionAfterptrT = positionAfterptrT1;
      }
      if (EverParseIsError(positionAfterptrT))
      {
        positionAfterf = positionAfterptrT;
      }
      else
      {
        /* Validating field g */
        /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
        hasBytes = (InputLength - positionAfterptrT) >= 4ULL;
        if (hasBytes)
        {
          positionAfterg = positionAfterptrT + 4ULL;
        }
        else
        {
          positionAfterg =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAfterptrT);
        }
        if (EverParseIsSuccess(positionAfterg))
        {
          res = positionAfterg;
        }
        else
        {
          ErrorHandlerFn("_S32_Attempt",
            "g",
            EverParseErrorReasonOfResult(positionAfterg),
            EverParseGetValidatorErrorKind(positionAfterg),
            Ctxt,
            Input,
            positionAfterptrT);
          res = positionAfterg;
        }
        positionAfterf = res;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterf))
  {
    return positionAfterf;
  }
  ErrorHandlerFn("_S32_Attempt",
    "f",
    EverParseErrorReasonOfResult(positionAfterf),
    EverParseGetValidatorErrorKind(positionAfterf),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterf;
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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterf0;
  uint64_t positionAfterf;
  uint32_t f;
  BOOLEAN hasBytes;
  uint64_t positionAfterptrS0;
  uint64_t positionAfterptrS;
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
  if (hasBytes0)
  {
    positionAfterf0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterf0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterf0))
  {
    positionAfterf = positionAfterf0;
  }
  else
  {
    ErrorHandlerFn("_R32_Attempt",
      "f",
      EverParseErrorReasonOfResult(positionAfterf0),
      EverParseGetValidatorErrorKind(positionAfterf0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterf = positionAfterf0;
  }
  if (EverParseIsError(positionAfterf))
  {
    return positionAfterf;
  }
  f = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterf) >= 4ULL;
  if (hasBytes)
  {
    positionAfterptrS0 = positionAfterf + 4ULL;
  }
  else
  {
    positionAfterptrS0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterf);
  }
  if (EverParseIsError(positionAfterptrS0))
  {
    positionAfterptrS = positionAfterptrS0;
  }
  else
  {
    ptrS = Load32Le(Input + (uint32_t)positionAfterf);
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
        positionAfterf);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterptrS = positionAfterptrS0;
    }
    else
    {
      positionAfterptrS =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptrS0);
    }
  }
  if (EverParseIsSuccess(positionAfterptrS))
  {
    return positionAfterptrS;
  }
  ErrorHandlerFn("_R32_Attempt",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterptrS),
    EverParseGetValidatorErrorKind(positionAfterptrS),
    Ctxt,
    Input,
    positionAfterf);
  return positionAfterptrS;
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
  uint64_t positionAfterr32;
  uint64_t positionAfterr64;
  if (Requestor32)
  {
    /* Validating field r32 */
    positionAfterr32 =
      ValidateR32Attempt(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterr32))
    {
      return positionAfterr32;
    }
    ErrorHandlerFn("_RMux",
      "r32",
      EverParseErrorReasonOfResult(positionAfterr32),
      EverParseGetValidatorErrorKind(positionAfterr32),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterr32;
  }
  /* Validating field r64 */
  positionAfterr64 =
    ValidateR64(RmuxProbeFieldR640T,
      RmuxProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterr64))
  {
    return positionAfterr64;
  }
  ErrorHandlerFn("_RMux",
    "r64",
    EverParseErrorReasonOfResult(positionAfterr64),
    EverParseGetValidatorErrorKind(positionAfterr64),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterr64;
}

