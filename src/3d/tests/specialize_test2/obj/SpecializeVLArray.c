

#include "SpecializeVLArray.h"

#include "SpecializeVLArray_ExternalAPI.h"

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
  uint32_t v = ProbeAndReadU32(Failed, rd, Src, Dest);
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
  uint64_t res11 = UlongToPtr(res1);
  BOOLEAN hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, Fieldname, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = WriteU64(res11, wr, Dest);
  if (ok)
  {
    *WriteOffset = wr + 8ULL;
    return;
  }
  *Failed = TRUE;
}

static void
Specialized32ProbeUnknownHeader64(
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
    Err(Tn, Fn, "NameLength", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  SkipBytesWrite(4ULL, WriteOffset, Failed);
  BOOLEAN hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, "alignment", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  ReadAndCoercePointer("pName",
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
    Err(Tn, Fn, "pName", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  ReadAndCoercePointer("pRawValue",
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
  BOOLEAN hasFailed3 = *Failed;
  if (hasFailed3)
  {
    Err(Tn, Fn, "pRawValue", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint64_t
ValidateUnknownHeadersInternal64(
  uint16_t UnknownHeaderCount,
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
  /* Validating field UnknownHeaders */
  uint64_t res;
  if (24U * (uint32_t)UnknownHeaderCount % 24U == 0U)
  {
    BOOLEAN
    hasBytes = (uint64_t)(24U * (uint32_t)UnknownHeaderCount) <= (InputLength - StartPosition);
    if (hasBytes)
    {
      res = StartPosition + (uint64_t)(24U * (uint32_t)UnknownHeaderCount);
    }
    else
    {
      res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
    }
  }
  else
  {
    res =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE,
        StartPosition);
  }
  uint64_t positionAfterUnknownHeadersInternal64 = res;
  if (EverParseIsSuccess(positionAfterUnknownHeadersInternal64))
  {
    return positionAfterUnknownHeadersInternal64;
  }
  ErrorHandlerFn("_UNKNOWN_HEADERS_INTERNAL_64",
    "UnknownHeaders",
    EverParseErrorReasonOfResult(positionAfterUnknownHeadersInternal64),
    EverParseGetValidatorErrorKind(positionAfterUnknownHeadersInternal64),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterUnknownHeadersInternal64;
}

static void
Specialized32ProbeUnknownHeadersInternal64(
  uint16_t UnknownHeaderCount,
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
  uint64_t ctr = (uint64_t)(12U * (uint32_t)UnknownHeaderCount);
  uint64_t c0 = ctr;
  BOOLEAN hasFailed = *Failed;
  BOOLEAN cond = c0 != 0ULL && !hasFailed;
  while (cond)
  {
    uint64_t r0 = *ReadOffset;
    Specialized32ProbeUnknownHeader64(Tn,
      Fn,
      Det,
      Ctxt,
      Err,
      ReadOffset,
      WriteOffset,
      Failed,
      Src,
      Dest);
    BOOLEAN hasFailed0 = *Failed;
    if (hasFailed0)
    {
      Err(Tn, Fn, "UnknownHeaders", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
    BOOLEAN hasFailed1 = *Failed;
    uint64_t r1 = *ReadOffset;
    uint64_t bytesRead = r1 - r0;
    uint64_t c = ctr;
    if (hasFailed1 || bytesRead == 0ULL || c < bytesRead)
    {
      Err(Tn, Fn, Det, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      *Failed = TRUE;
    }
    else
    {
      ctr = c - bytesRead;
    }
    uint64_t c1 = ctr;
    BOOLEAN hasFailed2 = *Failed;
    cond = c1 != 0ULL && !hasFailed2;
  }
}

static inline uint64_t
ValidateUnknownHeaders64(
  void
  (*ProbePUnknownHeaders)(
    uint16_t x0,
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
  uint16_t UnknownHeaderCount,
  EVERPARSE_COPY_BUFFER_T UnknownHeaderProbe,
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
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - StartPosition);
  uint64_t positionAfterpUnknownHeaders;
  if (hasBytes)
  {
    positionAfterpUnknownHeaders = StartPosition + 8ULL;
  }
  else
  {
    positionAfterpUnknownHeaders =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterUnknownHeaders64;
  if (EverParseIsError(positionAfterpUnknownHeaders))
  {
    positionAfterUnknownHeaders64 = positionAfterpUnknownHeaders;
  }
  else
  {
    uint64_t pUnknownHeaders = Load64Le(Input + (uint32_t)StartPosition);
    uint64_t src64 = pUnknownHeaders;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN
    ok =
      ProbeInit("_UNKNOWN_HEADERS_64.pUnknownHeaders",
        (uint64_t)(24U * (uint32_t)UnknownHeaderCount),
        UnknownHeaderProbe);
    if (ok)
    {
      ProbePUnknownHeaders(UnknownHeaderCount,
        "_UNKNOWN_HEADERS_64",
        "pUnknownHeaders",
        "probe",
        Ctxt,
        ErrorHandlerFn,
        &readOffset,
        &writeOffset,
        &failed,
        src64,
        (uint64_t)(24U * (uint32_t)UnknownHeaderCount),
        UnknownHeaderProbe);
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
      ErrorHandlerFn("_UNKNOWN_HEADERS_64",
        "pUnknownHeaders",
        "probe",
        0ULL,
        Ctxt,
        EverParseStreamOf(UnknownHeaderProbe),
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
        ValidateUnknownHeadersInternal64(UnknownHeaderCount,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(UnknownHeaderProbe),
          EverParseStreamLen(UnknownHeaderProbe),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_UNKNOWN_HEADERS_64",
        "pUnknownHeaders",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        StartPosition);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterUnknownHeaders64 = positionAfterpUnknownHeaders;
    }
    else
    {
      positionAfterUnknownHeaders64 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterpUnknownHeaders);
    }
  }
  if (EverParseIsSuccess(positionAfterUnknownHeaders64))
  {
    return positionAfterUnknownHeaders64;
  }
  ErrorHandlerFn("_UNKNOWN_HEADERS_64",
    "pUnknownHeaders",
    EverParseErrorReasonOfResult(positionAfterUnknownHeaders64),
    EverParseGetValidatorErrorKind(positionAfterUnknownHeaders64),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterUnknownHeaders64;
}

static inline uint64_t
ValidateSpecializedUnknownHeaders32(
  uint16_t UnknownHeaderCount,
  EVERPARSE_COPY_BUFFER_T UnknownHeaderProbe,
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
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - StartPosition);
  uint64_t positionAfterpUnknownHeaders;
  if (hasBytes)
  {
    positionAfterpUnknownHeaders = StartPosition + 8ULL;
  }
  else
  {
    positionAfterpUnknownHeaders =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterSpecializedUnknownHeaders32;
  if (EverParseIsError(positionAfterpUnknownHeaders))
  {
    positionAfterSpecializedUnknownHeaders32 = positionAfterpUnknownHeaders;
  }
  else
  {
    uint64_t pUnknownHeaders = Load64Le(Input + (uint32_t)StartPosition);
    uint64_t src64 = pUnknownHeaders;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN
    ok =
      ProbeInit("___specialized_UNKNOWN_HEADERS_32.pUnknownHeaders",
        (uint64_t)(24U * (uint32_t)UnknownHeaderCount),
        UnknownHeaderProbe);
    if (ok)
    {
      Specialized32ProbeUnknownHeadersInternal64(UnknownHeaderCount,
        "___specialized_UNKNOWN_HEADERS_32",
        "pUnknownHeaders",
        "probe",
        Ctxt,
        ErrorHandlerFn,
        &readOffset,
        &writeOffset,
        &failed,
        src64,
        UnknownHeaderProbe);
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
      ErrorHandlerFn("___specialized_UNKNOWN_HEADERS_32",
        "pUnknownHeaders",
        "probe",
        0ULL,
        Ctxt,
        EverParseStreamOf(UnknownHeaderProbe),
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
        ValidateUnknownHeadersInternal64(UnknownHeaderCount,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(UnknownHeaderProbe),
          EverParseStreamLen(UnknownHeaderProbe),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("___specialized_UNKNOWN_HEADERS_32",
        "pUnknownHeaders",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        StartPosition);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterSpecializedUnknownHeaders32 = positionAfterpUnknownHeaders;
    }
    else
    {
      positionAfterSpecializedUnknownHeaders32 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterpUnknownHeaders);
    }
  }
  if (EverParseIsSuccess(positionAfterSpecializedUnknownHeaders32))
  {
    return positionAfterSpecializedUnknownHeaders32;
  }
  ErrorHandlerFn("___specialized_UNKNOWN_HEADERS_32",
    "pUnknownHeaders",
    EverParseErrorReasonOfResult(positionAfterSpecializedUnknownHeaders32),
    EverParseGetValidatorErrorKind(positionAfterSpecializedUnknownHeaders32),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterSpecializedUnknownHeaders32;
}

static void
UnknownHeadersProbeUnknownHeaders640UnknownHeadersInternal64(
  uint16_t Arg0,
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
  BOOLEAN ok = ProbeAndCopy(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

uint64_t
SpecializeVlarrayValidateUnknownHeaders(
  BOOLEAN Requestor32,
  uint16_t UnknownHeaderCount,
  EVERPARSE_COPY_BUFFER_T UnknownHeaderProbe,
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
    /* Validating field pUnknownHeaders32 */
    uint64_t
    positionAfterUnknownHeaders =
      ValidateSpecializedUnknownHeaders32(UnknownHeaderCount,
        UnknownHeaderProbe,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterUnknownHeaders))
    {
      return positionAfterUnknownHeaders;
    }
    ErrorHandlerFn("_UNKNOWN_HEADERS",
      "pUnknownHeaders32",
      EverParseErrorReasonOfResult(positionAfterUnknownHeaders),
      EverParseGetValidatorErrorKind(positionAfterUnknownHeaders),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterUnknownHeaders;
  }
  if (Requestor32 == FALSE)
  {
    /* Validating field pUnknownHeaders64 */
    uint64_t
    positionAfterUnknownHeaders =
      ValidateUnknownHeaders64(UnknownHeadersProbeUnknownHeaders640UnknownHeadersInternal64,
        UnknownHeaderCount,
        UnknownHeaderProbe,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterUnknownHeaders))
    {
      return positionAfterUnknownHeaders;
    }
    ErrorHandlerFn("_UNKNOWN_HEADERS",
      "pUnknownHeaders64",
      EverParseErrorReasonOfResult(positionAfterUnknownHeaders),
      EverParseGetValidatorErrorKind(positionAfterUnknownHeaders),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterUnknownHeaders;
  }
  uint64_t
  positionAfterUnknownHeaders =
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
      StartPosition);
  if (EverParseIsSuccess(positionAfterUnknownHeaders))
  {
    return positionAfterUnknownHeaders;
  }
  ErrorHandlerFn("_UNKNOWN_HEADERS",
    "_x_0",
    EverParseErrorReasonOfResult(positionAfterUnknownHeaders),
    EverParseGetValidatorErrorKind(positionAfterUnknownHeaders),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterUnknownHeaders;
}

