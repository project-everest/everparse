

#include "SpecializeTaggedUnionArray.h"

#include "SpecializeTaggedUnionArray_ExternalAPI.h"

static inline uint64_t
ValidatePayload0(
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
  uint64_t positionAfterf0;
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
  uint64_t positionAfterPayload0;
  if (EverParseIsError(positionAfterf0))
  {
    positionAfterPayload0 = positionAfterf0;
  }
  else
  {
    uint32_t f0 = Load32Le(Input + (uint32_t)StartPosition);
    BOOLEAN
    f0ConstraintIsOk =
      f0 == (uint32_t)0U || f0 == (uint32_t)2U || f0 == (uint32_t)4U || f0 == (uint32_t)6U;
    uint64_t positionAfterf01 = EverParseCheckConstraintOk(f0ConstraintIsOk, positionAfterf0);
    if (EverParseIsError(positionAfterf01))
    {
      positionAfterPayload0 = positionAfterf01;
    }
    else
    {
      BOOLEAN hasBytes = 12ULL <= (InputLength - positionAfterf01);
      uint64_t res;
      if (hasBytes)
      {
        res = positionAfterf01 + 12ULL;
      }
      else
      {
        res =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterf01);
      }
      positionAfterPayload0 = res;
    }
  }
  if (EverParseIsSuccess(positionAfterPayload0))
  {
    return positionAfterPayload0;
  }
  ErrorHandlerFn("_PAYLOAD_0",
    "f0",
    EverParseErrorReasonOfResult(positionAfterPayload0),
    EverParseGetValidatorErrorKind(positionAfterPayload0),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPayload0;
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

static void SkipBytesRead(uint64_t Numbytes, uint64_t *ReadOffset, BOOLEAN *Failed)
{
  uint64_t rd = *ReadOffset;
  if (rd <= (0xffffffffffffffffULL - Numbytes))
  {
    *ReadOffset = rd + Numbytes;
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
Specialized32ProbePayload0(
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
    Err(Tn, Fn, "f0", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  SkipBytesWrite(4ULL, WriteOffset, Failed);
  BOOLEAN hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, "alignment", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  ReadAndCoercePointer("ptr",
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
    Err(Tn, Fn, "ptr", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static void
Specialized32ProbePayloadDefault(
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
  ReadAndCoercePointer("ptr1",
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
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "ptr1", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint64_t
ValidatePayload(
  uint64_t Tag,
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
  if (Tag == (uint64_t)0U)
  {
    /* Validating field p0 */
    uint64_t
    positionAfterPayload = ValidatePayload0(Ctxt, ErrorHandlerFn, Input, InputLen, StartPosition);
    if (EverParseIsSuccess(positionAfterPayload))
    {
      return positionAfterPayload;
    }
    ErrorHandlerFn("_PAYLOAD",
      "p0",
      EverParseErrorReasonOfResult(positionAfterPayload),
      EverParseGetValidatorErrorKind(positionAfterPayload),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterPayload;
  }
  BOOLEAN hasBytes = 16ULL <= (InputLen - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 16ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

static void
Specialized32ProbePayload(
  uint64_t Tag,
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
  if (Tag == (uint64_t)0U)
  {
    Specialized32ProbePayload0(Tn, Fn, Det, Ctxt, Err, ReadOffset, WriteOffset, Failed, Src, Dest);
    BOOLEAN hasFailed = *Failed;
    if (hasFailed)
    {
      Err(Tn, Fn, "p0", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      return;
    }
    return;
  }
  Specialized32ProbePayloadDefault(Tn,
    Fn,
    Det,
    Ctxt,
    Err,
    ReadOffset,
    WriteOffset,
    Failed,
    Src,
    Dest);
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "pdef", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
  }
  else
  {
    SkipBytesRead(4ULL, ReadOffset, Failed);
    BOOLEAN hasFailed1 = *Failed;
    if (hasFailed1)
    {
      Err(Tn, Fn, "alignment", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
    else
    {
      SkipBytesWrite(8ULL, WriteOffset, Failed);
      BOOLEAN hasFailed2 = *Failed;
      if (hasFailed2)
      {
        Err(Tn, Fn, "alignment", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      }
    }
  }
  BOOLEAN hasFailed0 = *Failed;
  if (hasFailed0)
  {
    Err(Tn, Fn, "__union_case_", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint64_t
ValidateWrapper(
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
  uint64_t positionAfterWrapper;
  if (hasBytes)
  {
    positionAfterWrapper = StartPosition + 8ULL;
  }
  else
  {
    positionAfterWrapper =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterTag;
  if (EverParseIsSuccess(positionAfterWrapper))
  {
    positionAfterTag = positionAfterWrapper;
  }
  else
  {
    ErrorHandlerFn("_WRAPPER",
      "Tag",
      EverParseErrorReasonOfResult(positionAfterWrapper),
      EverParseGetValidatorErrorKind(positionAfterWrapper),
      Ctxt,
      Input,
      StartPosition);
    positionAfterTag = positionAfterWrapper;
  }
  if (EverParseIsError(positionAfterTag))
  {
    return positionAfterTag;
  }
  uint64_t tag = Load64Le(Input + (uint32_t)StartPosition);
  /* Validating field payload */
  uint64_t
  positionAfterWrapper0 =
    ValidatePayload(tag,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAfterTag);
  if (EverParseIsSuccess(positionAfterWrapper0))
  {
    return positionAfterWrapper0;
  }
  ErrorHandlerFn("_WRAPPER",
    "payload",
    EverParseErrorReasonOfResult(positionAfterWrapper0),
    EverParseGetValidatorErrorKind(positionAfterWrapper0),
    Ctxt,
    Input,
    positionAfterTag);
  return positionAfterWrapper0;
}

static void
Specialized32ProbeWrapper(
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
  uint64_t v = ProbeAndReadU64(Failed, rd, Src, Dest);
  BOOLEAN hasFailed = *Failed;
  uint64_t res1;
  if (hasFailed)
  {
    Err(Tn, Fn, Det, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    res1 = v;
  }
  else
  {
    *ReadOffset = rd + 8ULL;
    res1 = v;
  }
  BOOLEAN hasFailed0 = *Failed;
  if (hasFailed0)
  {
    Err(Tn, Fn, "Tag", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t wr = *WriteOffset;
  BOOLEAN ok = WriteU64(res1, wr, Dest);
  if (ok)
  {
    *WriteOffset = wr + 8ULL;
  }
  else
  {
    *Failed = TRUE;
  }
  BOOLEAN hasFailed1 = *Failed;
  if (hasFailed1)
  {
    Err(Tn, Fn, "Tag", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  Specialized32ProbePayload(res1,
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
    Err(Tn, Fn, "payload", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint64_t
ValidateWrapperArray(
  uint16_t Count,
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
  /* Validating field Chunks */
  BOOLEAN hasEnoughBytes = (uint64_t)(24U * (uint32_t)Count) <= (InputLength - StartPosition);
  uint64_t positionAfterWrapperArray;
  if (!hasEnoughBytes)
  {
    positionAfterWrapperArray =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  else
  {
    uint8_t *truncatedInput = Input;
    uint64_t truncatedInputLength = StartPosition + (uint64_t)(24U * (uint32_t)Count);
    uint64_t result = StartPosition;
    while (TRUE)
    {
      uint64_t position = result;
      BOOLEAN ite;
      if (!(1ULL <= (truncatedInputLength - position)))
      {
        ite = TRUE;
      }
      else
      {
        uint64_t
        positionAfterWrapperArray0 =
          ValidateWrapper(Ctxt,
            ErrorHandlerFn,
            truncatedInput,
            truncatedInputLength,
            position);
        uint64_t result1;
        if (EverParseIsSuccess(positionAfterWrapperArray0))
        {
          result1 = positionAfterWrapperArray0;
        }
        else
        {
          ErrorHandlerFn("_WRAPPER_ARRAY",
            "Chunks.element",
            EverParseErrorReasonOfResult(positionAfterWrapperArray0),
            EverParseGetValidatorErrorKind(positionAfterWrapperArray0),
            Ctxt,
            truncatedInput,
            position);
          result1 = positionAfterWrapperArray0;
        }
        result = result1;
        ite = EverParseIsError(result1);
      }
      if (ite)
      {
        break;
      }
    }
    uint64_t res = result;
    positionAfterWrapperArray = res;
  }
  if (EverParseIsSuccess(positionAfterWrapperArray))
  {
    return positionAfterWrapperArray;
  }
  ErrorHandlerFn("_WRAPPER_ARRAY",
    "Chunks",
    EverParseErrorReasonOfResult(positionAfterWrapperArray),
    EverParseGetValidatorErrorKind(positionAfterWrapperArray),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterWrapperArray;
}

static void
Specialized32ProbeWrapperArray(
  uint16_t Count,
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
  uint64_t ctr = (uint64_t)(16U * (uint32_t)Count);
  uint64_t c0 = ctr;
  BOOLEAN hasFailed = *Failed;
  BOOLEAN cond = c0 != 0ULL && !hasFailed;
  while (cond)
  {
    uint64_t r0 = *ReadOffset;
    Specialized32ProbeWrapper(Tn, Fn, Det, Ctxt, Err, ReadOffset, WriteOffset, Failed, Src, Dest);
    BOOLEAN hasFailed0 = *Failed;
    if (hasFailed0)
    {
      Err(Tn, Fn, "Chunks", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
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
ValidateWrapper64(
  void
  (*ProbeChunks)(
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
  uint16_t Count,
  EVERPARSE_COPY_BUFFER_T Out,
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
  uint64_t positionAfterChunks;
  if (hasBytes)
  {
    positionAfterChunks = StartPosition + 8ULL;
  }
  else
  {
    positionAfterChunks =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterWrapper64;
  if (EverParseIsError(positionAfterChunks))
  {
    positionAfterWrapper64 = positionAfterChunks;
  }
  else
  {
    uint64_t chunks = Load64Le(Input + (uint32_t)StartPosition);
    uint64_t src64 = chunks;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit("_WRAPPER_64.Chunks", (uint64_t)(24U * (uint32_t)Count), Out);
    if (ok)
    {
      ProbeChunks(Count,
        "_WRAPPER_64",
        "Chunks",
        "probe",
        Ctxt,
        ErrorHandlerFn,
        &readOffset,
        &writeOffset,
        &failed,
        src64,
        (uint64_t)(24U * (uint32_t)Count),
        Out);
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
      ErrorHandlerFn("_WRAPPER_64", "Chunks", "probe", 0ULL, Ctxt, EverParseStreamOf(Out), 0ULL);
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
        ValidateWrapperArray(Count,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(Out),
          EverParseStreamLen(Out),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_WRAPPER_64",
        "Chunks",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        StartPosition);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterWrapper64 = positionAfterChunks;
    }
    else
    {
      positionAfterWrapper64 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterChunks);
    }
  }
  if (EverParseIsSuccess(positionAfterWrapper64))
  {
    return positionAfterWrapper64;
  }
  ErrorHandlerFn("_WRAPPER_64",
    "Chunks",
    EverParseErrorReasonOfResult(positionAfterWrapper64),
    EverParseGetValidatorErrorKind(positionAfterWrapper64),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterWrapper64;
}

static inline uint64_t
ValidateSpecializedWrapper32(
  uint16_t Count,
  EVERPARSE_COPY_BUFFER_T Out,
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
  uint64_t positionAfterChunks;
  if (hasBytes)
  {
    positionAfterChunks = StartPosition + 8ULL;
  }
  else
  {
    positionAfterChunks =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterSpecializedWrapper32;
  if (EverParseIsError(positionAfterChunks))
  {
    positionAfterSpecializedWrapper32 = positionAfterChunks;
  }
  else
  {
    uint64_t chunks = Load64Le(Input + (uint32_t)StartPosition);
    uint64_t src64 = chunks;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN
    ok = ProbeInit("___specialized_WRAPPER_32.Chunks", (uint64_t)(24U * (uint32_t)Count), Out);
    if (ok)
    {
      Specialized32ProbeWrapperArray(Count,
        "___specialized_WRAPPER_32",
        "Chunks",
        "probe",
        Ctxt,
        ErrorHandlerFn,
        &readOffset,
        &writeOffset,
        &failed,
        src64,
        Out);
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
      ErrorHandlerFn("___specialized_WRAPPER_32",
        "Chunks",
        "probe",
        0ULL,
        Ctxt,
        EverParseStreamOf(Out),
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
        ValidateWrapperArray(Count,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(Out),
          EverParseStreamLen(Out),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("___specialized_WRAPPER_32",
        "Chunks",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        StartPosition);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterSpecializedWrapper32 = positionAfterChunks;
    }
    else
    {
      positionAfterSpecializedWrapper32 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterChunks);
    }
  }
  if (EverParseIsSuccess(positionAfterSpecializedWrapper32))
  {
    return positionAfterSpecializedWrapper32;
  }
  ErrorHandlerFn("___specialized_WRAPPER_32",
    "Chunks",
    EverParseErrorReasonOfResult(positionAfterSpecializedWrapper32),
    EverParseGetValidatorErrorKind(positionAfterSpecializedWrapper32),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterSpecializedWrapper32;
}

static void
MainProbeWrapper640WrapperArray(
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
SpecializeTaggedUnionArrayValidateMain(
  BOOLEAN Requestor32,
  uint16_t Count,
  EVERPARSE_COPY_BUFFER_T Out,
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
    /* Validating field w32 */
    uint64_t
    positionAfterMain =
      ValidateSpecializedWrapper32(Count,
        Out,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterMain))
    {
      return positionAfterMain;
    }
    ErrorHandlerFn("_MAIN",
      "w32",
      EverParseErrorReasonOfResult(positionAfterMain),
      EverParseGetValidatorErrorKind(positionAfterMain),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterMain;
  }
  /* Validating field w64 */
  uint64_t
  positionAfterMain =
    ValidateWrapper64(MainProbeWrapper640WrapperArray,
      Count,
      Out,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLen,
      StartPosition);
  if (EverParseIsSuccess(positionAfterMain))
  {
    return positionAfterMain;
  }
  ErrorHandlerFn("_MAIN",
    "w64",
    EverParseErrorReasonOfResult(positionAfterMain),
    EverParseGetValidatorErrorKind(positionAfterMain),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterMain;
}

