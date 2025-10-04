

#include "Specialize1.h"

#include "Specialize1_ExternalAPI.h"

static inline uint64_t
ValidateT(
  uint32_t Bound,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field t1 */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterT;
  if (hasBytes0)
  {
    positionAfterT = StartPosition + 4ULL;
  }
  else
  {
    positionAfterT =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterT))
  {
    res = positionAfterT;
  }
  else
  {
    ErrorHandlerFn("_T",
      "t1",
      EverParseErrorReasonOfResult(positionAfterT),
      EverParseGetValidatorErrorKind(positionAfterT),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterT;
  }
  uint64_t positionAftert1 = res;
  if (EverParseIsError(positionAftert1))
  {
    return positionAftert1;
  }
  /* Validating field t2 */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = 4ULL <= (InputLength - positionAftert1);
  uint64_t positionAftert2_refinement;
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
  uint64_t positionAfterT0;
  if (EverParseIsError(positionAftert2_refinement))
  {
    positionAfterT0 = positionAftert2_refinement;
  }
  else
  {
    /* reading field_value */
    uint32_t t2_refinement = Load32Le(Input + (uint32_t)positionAftert1);
    /* start: checking constraint */
    BOOLEAN t2_refinementConstraintIsOk = t2_refinement <= Bound;
    /* end: checking constraint */
    positionAfterT0 =
      EverParseCheckConstraintOk(t2_refinementConstraintIsOk,
        positionAftert2_refinement);
  }
  if (EverParseIsSuccess(positionAfterT0))
  {
    return positionAfterT0;
  }
  ErrorHandlerFn("_T",
    "t2.refinement",
    EverParseErrorReasonOfResult(positionAfterT0),
    EverParseGetValidatorErrorKind(positionAfterT0),
    Ctxt,
    Input,
    positionAftert1);
  return positionAfterT0;
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
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
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
  BOOLEAN hasFailed0 = *Failed;
  if (hasFailed0)
  {
    Err(Tn, Fn, Fieldname, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t res11 = UlongToPtr1(res1);
  BOOLEAN hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, Fieldname, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = WriteU641(res11, wr, Dest);
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
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
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
  KRML_MAYBE_UNUSED_VAR(Bound);
  KRML_MAYBE_UNUSED_VAR(Det);
  KRML_MAYBE_UNUSED_VAR(Sz);
  CopyBytes(8ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  BOOLEAN hasFailed = *Failed;
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
    void
    (*x5)(
      EVERPARSE_STRING x0,
      EVERPARSE_STRING x1,
      EVERPARSE_STRING x2,
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
  uint32_t Bound,
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfters1;
  if (hasBytes0)
  {
    positionAfters1 = StartPosition + 4ULL;
  }
  else
  {
    positionAfters1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterS64;
  if (EverParseIsError(positionAfters1))
  {
    positionAfterS64 = positionAfters1;
  }
  else
  {
    uint32_t s1 = Load32Le(Input + (uint32_t)StartPosition);
    BOOLEAN s1ConstraintIsOk = s1 <= Bound;
    uint64_t positionAfters11 = EverParseCheckConstraintOk(s1ConstraintIsOk, positionAfters1);
    if (EverParseIsError(positionAfters11))
    {
      positionAfterS64 = positionAfters11;
    }
    else
    {
      /* Validating field ___alignment_padding_4 */
      BOOLEAN hasBytes1 = (uint64_t)4U <= (InputLength - positionAfters11);
      uint64_t res0;
      if (hasBytes1)
      {
        res0 = positionAfters11 + (uint64_t)4U;
      }
      else
      {
        res0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfters11);
      }
      uint64_t positionAfterS640 = res0;
      uint64_t positionAfterAlignmentPadding4;
      if (EverParseIsSuccess(positionAfterS640))
      {
        positionAfterAlignmentPadding4 = positionAfterS640;
      }
      else
      {
        ErrorHandlerFn("_S64",
          "___alignment_padding_4",
          EverParseErrorReasonOfResult(positionAfterS640),
          EverParseGetValidatorErrorKind(positionAfterS640),
          Ctxt,
          Input,
          positionAfters11);
        positionAfterAlignmentPadding4 = positionAfterS640;
      }
      if (EverParseIsError(positionAfterAlignmentPadding4))
      {
        positionAfterS64 = positionAfterAlignmentPadding4;
      }
      else
      {
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        BOOLEAN hasBytes2 = 8ULL <= (InputLength - positionAfterAlignmentPadding4);
        uint64_t positionAfterptrT0;
        if (hasBytes2)
        {
          positionAfterptrT0 = positionAfterAlignmentPadding4 + 8ULL;
        }
        else
        {
          positionAfterptrT0 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAfterAlignmentPadding4);
        }
        uint64_t positionAfterS641;
        if (EverParseIsError(positionAfterptrT0))
        {
          positionAfterS641 = positionAfterptrT0;
        }
        else
        {
          uint64_t ptrT = Load64Le(Input + (uint32_t)positionAfterAlignmentPadding4);
          uint64_t src64 = ptrT;
          uint64_t readOffset = 0ULL;
          uint64_t writeOffset = 0ULL;
          BOOLEAN failed = FALSE;
          BOOLEAN ok = ProbeInit1("_S64.ptrT", (uint64_t)8U, Dest);
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
          uint64_t wr = writeOffset;
          BOOLEAN hasFailed = failed;
          uint64_t b;
          if (hasFailed)
          {
            ErrorHandlerFn("_S64", "ptrT", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
            b = 0ULL;
          }
          else
          {
            b = wr;
          }
          BOOLEAN actionResult;
          if (b != 0ULL)
          {
            uint64_t
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
              positionAfterAlignmentPadding4);
            actionResult = FALSE;
          }
          if (actionResult)
          {
            positionAfterS641 = positionAfterptrT0;
          }
          else
          {
            positionAfterS641 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
                positionAfterptrT0);
          }
        }
        uint64_t positionAfterptrT;
        if (EverParseIsSuccess(positionAfterS641))
        {
          positionAfterptrT = positionAfterS641;
        }
        else
        {
          ErrorHandlerFn("_S64",
            "ptrT",
            EverParseErrorReasonOfResult(positionAfterS641),
            EverParseGetValidatorErrorKind(positionAfterS641),
            Ctxt,
            Input,
            positionAfterAlignmentPadding4);
          positionAfterptrT = positionAfterS641;
        }
        if (EverParseIsError(positionAfterptrT))
        {
          positionAfterS64 = positionAfterptrT;
        }
        else
        {
          BOOLEAN hasBytes = 8ULL <= (InputLength - positionAfterptrT);
          uint64_t res;
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
          positionAfterS64 = res;
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfterS64))
  {
    return positionAfterS64;
  }
  ErrorHandlerFn("_S64",
    "s1",
    EverParseErrorReasonOfResult(positionAfterS64),
    EverParseGetValidatorErrorKind(positionAfterS64),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterS64;
}

static void
Specialized32ProbeS64(
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  CopyBytes(4ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "s1", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  SkipBytesWrite(4ULL, WriteOffset, Failed);
  BOOLEAN hasFailed1 = *Failed;
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
  BOOLEAN hasFailed2 = *Failed;
  if (hasFailed2)
  {
    Err(Tn, Fn, "ptrT", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  CopyBytes(4ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  BOOLEAN hasFailed3 = *Failed;
  if (hasFailed3)
  {
    Err(Tn, Fn, "s2", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  SkipBytesWrite(4ULL, WriteOffset, Failed);
  BOOLEAN hasFailed4 = *Failed;
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
    void
    (*x5)(
      EVERPARSE_STRING x0,
      EVERPARSE_STRING x1,
      EVERPARSE_STRING x2,
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
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterR64;
  if (hasBytes0)
  {
    positionAfterR64 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterR64 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterr1;
  if (EverParseIsSuccess(positionAfterR64))
  {
    positionAfterr1 = positionAfterR64;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "r1",
      EverParseErrorReasonOfResult(positionAfterR64),
      EverParseGetValidatorErrorKind(positionAfterR64),
      Ctxt,
      Input,
      StartPosition);
    positionAfterr1 = positionAfterR64;
  }
  if (EverParseIsError(positionAfterr1))
  {
    return positionAfterr1;
  }
  uint32_t r1 = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field ___alignment_padding_6 */
  BOOLEAN hasBytes1 = (uint64_t)4U <= (InputLength - positionAfterr1);
  uint64_t res;
  if (hasBytes1)
  {
    res = positionAfterr1 + (uint64_t)4U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, positionAfterr1);
  }
  uint64_t positionAfterR640 = res;
  uint64_t positionAfterAlignmentPadding6;
  if (EverParseIsSuccess(positionAfterR640))
  {
    positionAfterAlignmentPadding6 = positionAfterR640;
  }
  else
  {
    ErrorHandlerFn("_R64",
      "___alignment_padding_6",
      EverParseErrorReasonOfResult(positionAfterR640),
      EverParseGetValidatorErrorKind(positionAfterR640),
      Ctxt,
      Input,
      positionAfterr1);
    positionAfterAlignmentPadding6 = positionAfterR640;
  }
  if (EverParseIsError(positionAfterAlignmentPadding6))
  {
    return positionAfterAlignmentPadding6;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - positionAfterAlignmentPadding6);
  uint64_t positionAfterptrS;
  if (hasBytes)
  {
    positionAfterptrS = positionAfterAlignmentPadding6 + 8ULL;
  }
  else
  {
    positionAfterptrS =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterAlignmentPadding6);
  }
  uint64_t positionAfterR641;
  if (EverParseIsError(positionAfterptrS))
  {
    positionAfterR641 = positionAfterptrS;
  }
  else
  {
    uint64_t ptrS = Load64Le(Input + (uint32_t)positionAfterAlignmentPadding6);
    uint64_t src64 = ptrS;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit1("_R64.ptrS", (uint64_t)24U, DestS);
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
    uint64_t wr = writeOffset;
    BOOLEAN hasFailed = failed;
    uint64_t b;
    if (hasFailed)
    {
      ErrorHandlerFn("_R64", "ptrS", "probe", 0ULL, Ctxt, EverParseStreamOf(DestS), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    BOOLEAN actionResult;
    if (b != 0ULL)
    {
      uint64_t
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
        positionAfterAlignmentPadding6);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterR641 = positionAfterptrS;
    }
    else
    {
      positionAfterR641 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptrS);
    }
  }
  if (EverParseIsSuccess(positionAfterR641))
  {
    return positionAfterR641;
  }
  ErrorHandlerFn("_R64",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterR641),
    EverParseGetValidatorErrorKind(positionAfterR641),
    Ctxt,
    Input,
    positionAfterAlignmentPadding6);
  return positionAfterR641;
}

static inline uint64_t
ValidateSpecializedR32(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterSpecializedR32;
  if (hasBytes0)
  {
    positionAfterSpecializedR32 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterSpecializedR32 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterr1;
  if (EverParseIsSuccess(positionAfterSpecializedR32))
  {
    positionAfterr1 = positionAfterSpecializedR32;
  }
  else
  {
    ErrorHandlerFn("___specialized_R32",
      "r1",
      EverParseErrorReasonOfResult(positionAfterSpecializedR32),
      EverParseGetValidatorErrorKind(positionAfterSpecializedR32),
      Ctxt,
      Input,
      StartPosition);
    positionAfterr1 = positionAfterSpecializedR32;
  }
  if (EverParseIsError(positionAfterr1))
  {
    return positionAfterr1;
  }
  uint32_t r1 = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = 4ULL <= (InputLength - positionAfterr1);
  uint64_t positionAfterptrS;
  if (hasBytes)
  {
    positionAfterptrS = positionAfterr1 + 4ULL;
  }
  else
  {
    positionAfterptrS =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterr1);
  }
  uint64_t positionAfterSpecializedR320;
  if (EverParseIsError(positionAfterptrS))
  {
    positionAfterSpecializedR320 = positionAfterptrS;
  }
  else
  {
    uint32_t ptrS = Load32Le(Input + (uint32_t)positionAfterr1);
    uint64_t src64 = UlongToPtr1(ptrS);
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit1("___specialized_R32.ptrS", (uint64_t)24U, DestS);
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
    uint64_t wr = writeOffset;
    BOOLEAN hasFailed = failed;
    uint64_t b;
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
    BOOLEAN actionResult;
    if (b != 0ULL)
    {
      uint64_t
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
      positionAfterSpecializedR320 = positionAfterptrS;
    }
    else
    {
      positionAfterSpecializedR320 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptrS);
    }
  }
  if (EverParseIsSuccess(positionAfterSpecializedR320))
  {
    return positionAfterSpecializedR320;
  }
  ErrorHandlerFn("___specialized_R32",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterSpecializedR320),
    EverParseGetValidatorErrorKind(positionAfterSpecializedR320),
    Ctxt,
    Input,
    positionAfterr1);
  return positionAfterSpecializedR320;
}

static void
RProbeFieldR640T(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
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
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Det);
  uint64_t res1 = Sz;
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t rd = *ReadOffset;
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
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
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
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
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Det);
  uint64_t res1 = Sz;
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t rd = *ReadOffset;
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
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
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  if (Requestor32)
  {
    /* Validating field r32 */
    uint64_t
    positionAfterR =
      ValidateSpecializedR32(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterR))
    {
      return positionAfterR;
    }
    ErrorHandlerFn("___R",
      "r32",
      EverParseErrorReasonOfResult(positionAfterR),
      EverParseGetValidatorErrorKind(positionAfterR),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterR;
  }
  /* Validating field r64 */
  uint64_t
  positionAfterR =
    ValidateR64(RProbeFieldR640T,
      RProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterR))
  {
    return positionAfterR;
  }
  ErrorHandlerFn("___R",
    "r64",
    EverParseErrorReasonOfResult(positionAfterR),
    EverParseGetValidatorErrorKind(positionAfterR),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterR;
}

static void
S32attemptProbePtrTT(
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
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
  uint64_t res1 = Sz;
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t rd = *ReadOffset;
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
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
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterf;
  if (hasBytes0)
  {
    positionAfterf = StartPosition + 4ULL;
  }
  else
  {
    positionAfterf =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterS32Attempt;
  if (EverParseIsError(positionAfterf))
  {
    positionAfterS32Attempt = positionAfterf;
  }
  else
  {
    uint32_t f = Load32Le(Input + (uint32_t)StartPosition);
    BOOLEAN fConstraintIsOk = f <= Bound;
    uint64_t positionAfterf1 = EverParseCheckConstraintOk(fConstraintIsOk, positionAfterf);
    if (EverParseIsError(positionAfterf1))
    {
      positionAfterS32Attempt = positionAfterf1;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      BOOLEAN hasBytes1 = 4ULL <= (InputLength - positionAfterf1);
      uint64_t positionAfterptrT0;
      if (hasBytes1)
      {
        positionAfterptrT0 = positionAfterf1 + 4ULL;
      }
      else
      {
        positionAfterptrT0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterf1);
      }
      uint64_t positionAfterS32Attempt0;
      if (EverParseIsError(positionAfterptrT0))
      {
        positionAfterS32Attempt0 = positionAfterptrT0;
      }
      else
      {
        uint32_t ptrT = Load32Le(Input + (uint32_t)positionAfterf1);
        uint64_t src64 = UlongToPtr1(ptrT);
        uint64_t readOffset = 0ULL;
        uint64_t writeOffset = 0ULL;
        BOOLEAN failed = FALSE;
        BOOLEAN ok = ProbeInit1("_S32_Attempt.ptrT", (uint64_t)8U, Dest);
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
        uint64_t wr = writeOffset;
        BOOLEAN hasFailed = failed;
        uint64_t b;
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
        BOOLEAN actionResult;
        if (b != 0ULL)
        {
          uint64_t
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
            positionAfterf1);
          actionResult = FALSE;
        }
        if (actionResult)
        {
          positionAfterS32Attempt0 = positionAfterptrT0;
        }
        else
        {
          positionAfterS32Attempt0 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
              positionAfterptrT0);
        }
      }
      uint64_t positionAfterptrT;
      if (EverParseIsSuccess(positionAfterS32Attempt0))
      {
        positionAfterptrT = positionAfterS32Attempt0;
      }
      else
      {
        ErrorHandlerFn("_S32_Attempt",
          "ptrT",
          EverParseErrorReasonOfResult(positionAfterS32Attempt0),
          EverParseGetValidatorErrorKind(positionAfterS32Attempt0),
          Ctxt,
          Input,
          positionAfterf1);
        positionAfterptrT = positionAfterS32Attempt0;
      }
      if (EverParseIsError(positionAfterptrT))
      {
        positionAfterS32Attempt = positionAfterptrT;
      }
      else
      {
        /* Validating field g */
        /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
        BOOLEAN hasBytes = 4ULL <= (InputLength - positionAfterptrT);
        uint64_t positionAfterS32Attempt1;
        if (hasBytes)
        {
          positionAfterS32Attempt1 = positionAfterptrT + 4ULL;
        }
        else
        {
          positionAfterS32Attempt1 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAfterptrT);
        }
        uint64_t res;
        if (EverParseIsSuccess(positionAfterS32Attempt1))
        {
          res = positionAfterS32Attempt1;
        }
        else
        {
          ErrorHandlerFn("_S32_Attempt",
            "g",
            EverParseErrorReasonOfResult(positionAfterS32Attempt1),
            EverParseGetValidatorErrorKind(positionAfterS32Attempt1),
            Ctxt,
            Input,
            positionAfterptrT);
          res = positionAfterS32Attempt1;
        }
        positionAfterS32Attempt = res;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterS32Attempt))
  {
    return positionAfterS32Attempt;
  }
  ErrorHandlerFn("_S32_Attempt",
    "f",
    EverParseErrorReasonOfResult(positionAfterS32Attempt),
    EverParseGetValidatorErrorKind(positionAfterS32Attempt),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterS32Attempt;
}

static void
R32AttemptProbePtrSS32attempt(
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
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
  uint64_t res1 = Sz;
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t rd = *ReadOffset;
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
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
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterR32Attempt;
  if (hasBytes0)
  {
    positionAfterR32Attempt = StartPosition + 4ULL;
  }
  else
  {
    positionAfterR32Attempt =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterf;
  if (EverParseIsSuccess(positionAfterR32Attempt))
  {
    positionAfterf = positionAfterR32Attempt;
  }
  else
  {
    ErrorHandlerFn("_R32_Attempt",
      "f",
      EverParseErrorReasonOfResult(positionAfterR32Attempt),
      EverParseGetValidatorErrorKind(positionAfterR32Attempt),
      Ctxt,
      Input,
      StartPosition);
    positionAfterf = positionAfterR32Attempt;
  }
  if (EverParseIsError(positionAfterf))
  {
    return positionAfterf;
  }
  uint32_t f = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = 4ULL <= (InputLength - positionAfterf);
  uint64_t positionAfterptrS;
  if (hasBytes)
  {
    positionAfterptrS = positionAfterf + 4ULL;
  }
  else
  {
    positionAfterptrS =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterf);
  }
  uint64_t positionAfterR32Attempt0;
  if (EverParseIsError(positionAfterptrS))
  {
    positionAfterR32Attempt0 = positionAfterptrS;
  }
  else
  {
    uint32_t ptrS = Load32Le(Input + (uint32_t)positionAfterf);
    uint64_t src64 = UlongToPtr1(ptrS);
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit1("_R32_Attempt.ptrS", (uint64_t)12U, DestS);
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
    uint64_t wr = writeOffset;
    BOOLEAN hasFailed = failed;
    uint64_t b;
    if (hasFailed)
    {
      ErrorHandlerFn("_R32_Attempt", "ptrS", "probe", 0ULL, Ctxt, EverParseStreamOf(DestS), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    BOOLEAN actionResult;
    if (b != 0ULL)
    {
      uint64_t
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
      positionAfterR32Attempt0 = positionAfterptrS;
    }
    else
    {
      positionAfterR32Attempt0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptrS);
    }
  }
  if (EverParseIsSuccess(positionAfterR32Attempt0))
  {
    return positionAfterR32Attempt0;
  }
  ErrorHandlerFn("_R32_Attempt",
    "ptrS",
    EverParseErrorReasonOfResult(positionAfterR32Attempt0),
    EverParseGetValidatorErrorKind(positionAfterR32Attempt0),
    Ctxt,
    Input,
    positionAfterf);
  return positionAfterR32Attempt0;
}

static void
RmuxProbeFieldR640T(
  uint32_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Det,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
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
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Det);
  uint64_t res1 = Sz;
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t rd = *ReadOffset;
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
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
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
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
  KRML_MAYBE_UNUSED_VAR(Arg0);
  KRML_MAYBE_UNUSED_VAR(Det);
  uint64_t res1 = Sz;
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "probe_and_copy_init_sz", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t rd = *ReadOffset;
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = ProbeAndCopy1(res1, rd, wr, Src, Dest);
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
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  if (Requestor32)
  {
    /* Validating field r32 */
    uint64_t
    positionAfterRmux =
      ValidateR32Attempt(DestS,
        DestT,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterRmux))
    {
      return positionAfterRmux;
    }
    ErrorHandlerFn("_RMux",
      "r32",
      EverParseErrorReasonOfResult(positionAfterRmux),
      EverParseGetValidatorErrorKind(positionAfterRmux),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterRmux;
  }
  /* Validating field r64 */
  uint64_t
  positionAfterRmux =
    ValidateR64(RmuxProbeFieldR640T,
      RmuxProbeFieldR641S64,
      DestS,
      DestT,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterRmux))
  {
    return positionAfterRmux;
  }
  ErrorHandlerFn("_RMux",
    "r64",
    EverParseErrorReasonOfResult(positionAfterRmux),
    EverParseGetValidatorErrorKind(positionAfterRmux),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterRmux;
}

