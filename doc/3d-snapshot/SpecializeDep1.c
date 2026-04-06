

#include "SpecializeDep1.h"

#include "SpecializeDep1_ExternalAPI.h"

static inline uint64_t
ValidateUnion(
  uint8_t Tag,
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
  BOOLEAN hasBytes0;
  uint64_t positionAfterUnion;
  BOOLEAN hasBytes1;
  uint64_t positionAfterUnion0;
  BOOLEAN hasBytes;
  uint64_t positionAfterUnion1;
  if ((uint32_t)Tag == 0U)
  {
    /* Validating field case0 */
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    hasBytes0 = 1ULL <= (InputLen - StartPosition);
    if (hasBytes0)
    {
      positionAfterUnion = StartPosition + 1ULL;
    }
    else
    {
      positionAfterUnion =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterUnion))
    {
      return positionAfterUnion;
    }
    ErrorHandlerFn("_UNION",
      "case0",
      EverParseErrorReasonOfResult(positionAfterUnion),
      EverParseGetValidatorErrorKind(positionAfterUnion),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterUnion;
  }
  if ((uint32_t)Tag == 1U)
  {
    /* Validating field case1 */
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    hasBytes1 = 2ULL <= (InputLen - StartPosition);
    if (hasBytes1)
    {
      positionAfterUnion0 = StartPosition + 2ULL;
    }
    else
    {
      positionAfterUnion0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterUnion0))
    {
      return positionAfterUnion0;
    }
    ErrorHandlerFn("_UNION",
      "case1",
      EverParseErrorReasonOfResult(positionAfterUnion0),
      EverParseGetValidatorErrorKind(positionAfterUnion0),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterUnion0;
  }
  /* Validating field other */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = 4ULL <= (InputLen - StartPosition);
  if (hasBytes)
  {
    positionAfterUnion1 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterUnion1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterUnion1))
  {
    return positionAfterUnion1;
  }
  ErrorHandlerFn("_UNION",
    "other",
    EverParseErrorReasonOfResult(positionAfterUnion1),
    EverParseGetValidatorErrorKind(positionAfterUnion1),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterUnion1;
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
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  BOOLEAN hasFailed;
  BOOLEAN hasFailed0;
  BOOLEAN hasFailed1;
  BOOLEAN hasFailed2;
  if ((uint32_t)Tag == 0U)
  {
    CopyBytes(1ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
    hasFailed = *Failed;
    if (hasFailed)
    {
      Err(Tn, Fn, "case0", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  else if ((uint32_t)Tag == 1U)
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

static inline uint64_t
ValidateTlv(
  uint16_t Len,
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
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = 1ULL <= (InputLength - StartPosition);
  uint64_t positionAfterTlv;
  uint64_t positionAftertag;
  uint8_t tag;
  BOOLEAN hasBytes;
  uint64_t positionAfterlength;
  uint64_t positionAfterTlv0;
  uint32_t length;
  BOOLEAN lengthConstraintIsOk;
  uint64_t positionAfterlength1;
  BOOLEAN hasEnoughBytes;
  uint64_t positionAfterTlv1;
  uint8_t *truncatedInput;
  uint64_t truncatedInputLength;
  uint64_t result;
  uint64_t position;
  BOOLEAN ite;
  uint64_t positionAfterTlv2;
  uint64_t result1;
  uint64_t res;
  if (hasBytes0)
  {
    positionAfterTlv = StartPosition + 1ULL;
  }
  else
  {
    positionAfterTlv =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterTlv))
  {
    positionAftertag = positionAfterTlv;
  }
  else
  {
    ErrorHandlerFn("_TLV",
      "tag",
      EverParseErrorReasonOfResult(positionAfterTlv),
      EverParseGetValidatorErrorKind(positionAfterTlv),
      Ctxt,
      Input,
      StartPosition);
    positionAftertag = positionAfterTlv;
  }
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  tag = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = 4ULL <= (InputLength - positionAftertag);
  if (hasBytes)
  {
    positionAfterlength = positionAftertag + 4ULL;
  }
  else
  {
    positionAfterlength =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertag);
  }
  if (EverParseIsError(positionAfterlength))
  {
    positionAfterTlv0 = positionAfterlength;
  }
  else
  {
    length = Load32Le(Input + (uint32_t)positionAftertag);
    lengthConstraintIsOk = length == (uint32_t)Len;
    positionAfterlength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterlength);
    if (EverParseIsError(positionAfterlength1))
    {
      positionAfterTlv0 = positionAfterlength1;
    }
    else
    {
      /* Validating field payload */
      hasEnoughBytes = (uint64_t)(uint32_t)Len <= (InputLength - positionAfterlength1);
      if (!hasEnoughBytes)
      {
        positionAfterTlv1 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterlength1);
      }
      else
      {
        truncatedInput = Input;
        truncatedInputLength = positionAfterlength1 + (uint64_t)(uint32_t)Len;
        result = positionAfterlength1;
        while (TRUE)
        {
          position = result;
          if (!(1ULL <= (truncatedInputLength - position)))
          {
            ite = TRUE;
          }
          else
          {
            positionAfterTlv2 =
              ValidateUnion(tag,
                Ctxt,
                ErrorHandlerFn,
                truncatedInput,
                truncatedInputLength,
                position);
            if (EverParseIsSuccess(positionAfterTlv2))
            {
              result1 = positionAfterTlv2;
            }
            else
            {
              ErrorHandlerFn("_TLV",
                "payload.element",
                EverParseErrorReasonOfResult(positionAfterTlv2),
                EverParseGetValidatorErrorKind(positionAfterTlv2),
                Ctxt,
                truncatedInput,
                position);
              result1 = positionAfterTlv2;
            }
            result = result1;
            ite = EverParseIsError(result1);
          }
          if (ite)
          {
            break;
          }
        }
        res = result;
        positionAfterTlv1 = res;
      }
      if (EverParseIsSuccess(positionAfterTlv1))
      {
        positionAfterTlv0 = positionAfterTlv1;
      }
      else
      {
        ErrorHandlerFn("_TLV",
          "payload",
          EverParseErrorReasonOfResult(positionAfterTlv1),
          EverParseGetValidatorErrorKind(positionAfterTlv1),
          Ctxt,
          Input,
          positionAfterlength1);
        positionAfterTlv0 = positionAfterTlv1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterTlv0))
  {
    return positionAfterTlv0;
  }
  ErrorHandlerFn("_TLV",
    "length",
    EverParseErrorReasonOfResult(positionAfterTlv0),
    EverParseGetValidatorErrorKind(positionAfterTlv0),
    Ctxt,
    Input,
    positionAftertag);
  return positionAfterTlv0;
}

static void
Specialized32ProbeTlv(
  uint16_t Len,
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
  uint8_t v = ProbeAndReadU8(Failed, rd, Src, Dest);
  BOOLEAN hasFailed = *Failed;
  uint8_t res1;
  BOOLEAN hasFailed0;
  uint64_t wr;
  BOOLEAN ok;
  BOOLEAN hasFailed1;
  BOOLEAN hasFailed2;
  uint64_t ctr;
  uint64_t c0;
  BOOLEAN hasFailed3;
  BOOLEAN cond;
  uint64_t r0;
  BOOLEAN hasFailed30;
  BOOLEAN hasFailed31;
  uint64_t r1;
  uint64_t bytesRead;
  uint64_t c1;
  uint64_t c;
  BOOLEAN hasFailed32;
  if (hasFailed)
  {
    Err(Tn, Fn, Det, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
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
  c0 = ctr;
  hasFailed3 = *Failed;
  cond = c0 != 0ULL && !hasFailed3;
  while (cond)
  {
    r0 = *ReadOffset;
    Specialized32ProbeUnion(res1, Tn, Fn, Ctxt, Err, ReadOffset, WriteOffset, Failed, Src, Dest);
    hasFailed30 = *Failed;
    if (hasFailed30)
    {
      Err(Tn, Fn, "payload", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
    hasFailed31 = *Failed;
    r1 = *ReadOffset;
    bytesRead = r1 - r0;
    c1 = ctr;
    if (hasFailed31 || bytesRead == 0ULL || c1 < bytesRead)
    {
      Err(Tn, Fn, Det, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      *Failed = TRUE;
    }
    else
    {
      ctr = c1 - bytesRead;
    }
    c = ctr;
    hasFailed32 = *Failed;
    cond = c != 0ULL && !hasFailed32;
  }
}

static inline uint64_t
ValidateWrapper(
  void
  (*ProbeTlv)(
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
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
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
  uint64_t positionAfterPrecondition = StartPosition;
  uint64_t positionAfterWrapper;
  BOOLEAN preconditionConstraintIsOk;
  uint64_t positionAfterPrecondition1;
  BOOLEAN hasBytes;
  uint64_t positionAftertlv;
  uint64_t positionAfterWrapper0;
  uint64_t tlv;
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
  if (EverParseIsError(positionAfterPrecondition))
  {
    positionAfterWrapper = positionAfterPrecondition;
  }
  else
  {
    preconditionConstraintIsOk = (uint32_t)Len > (uint32_t)(uint16_t)5U;
    positionAfterPrecondition1 =
      EverParseCheckConstraintOk(preconditionConstraintIsOk,
        positionAfterPrecondition);
    if (EverParseIsError(positionAfterPrecondition1))
    {
      positionAfterWrapper = positionAfterPrecondition1;
    }
    else
    {
      /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
      hasBytes = 8ULL <= (InputLength - positionAfterPrecondition1);
      if (hasBytes)
      {
        positionAftertlv = positionAfterPrecondition1 + 8ULL;
      }
      else
      {
        positionAftertlv =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterPrecondition1);
      }
      if (EverParseIsError(positionAftertlv))
      {
        positionAfterWrapper0 = positionAftertlv;
      }
      else
      {
        tlv = Load64Le(Input + (uint32_t)positionAfterPrecondition1);
        src64 = tlv;
        readOffset = 0ULL;
        writeOffset = 0ULL;
        failed = FALSE;
        ok = ProbeInit("_WRAPPER.tlv", (uint64_t)Len, Output);
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
            (uint64_t)Len,
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
          result =
            ValidateTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
              Ctxt,
              ErrorHandlerFn,
              EverParseStreamOf(Output),
              EverParseStreamLen(Output),
              0ULL);
          actionResult = !EverParseIsError(result);
        }
        else
        {
          ErrorHandlerFn("_WRAPPER",
            "tlv",
            EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
            EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
            Ctxt,
            Input,
            positionAfterPrecondition1);
          actionResult = FALSE;
        }
        if (actionResult)
        {
          positionAfterWrapper0 = positionAftertlv;
        }
        else
        {
          positionAfterWrapper0 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
              positionAftertlv);
        }
      }
      if (EverParseIsSuccess(positionAfterWrapper0))
      {
        positionAfterWrapper = positionAfterWrapper0;
      }
      else
      {
        ErrorHandlerFn("_WRAPPER",
          "tlv",
          EverParseErrorReasonOfResult(positionAfterWrapper0),
          EverParseGetValidatorErrorKind(positionAfterWrapper0),
          Ctxt,
          Input,
          positionAfterPrecondition1);
        positionAfterWrapper = positionAfterWrapper0;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterWrapper))
  {
    return positionAfterWrapper;
  }
  ErrorHandlerFn("_WRAPPER",
    "__precondition",
    EverParseErrorReasonOfResult(positionAfterWrapper),
    EverParseGetValidatorErrorKind(positionAfterWrapper),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterWrapper;
}

static inline uint64_t
ValidateSpecializedWrapper32(
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
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
  uint64_t positionAfterPrecondition = StartPosition;
  uint64_t positionAfterSpecializedWrapper32;
  BOOLEAN preconditionConstraintIsOk;
  uint64_t positionAfterPrecondition1;
  BOOLEAN hasBytes;
  uint64_t positionAftertlv;
  uint64_t positionAfterSpecializedWrapper320;
  uint32_t tlv;
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
  if (EverParseIsError(positionAfterPrecondition))
  {
    positionAfterSpecializedWrapper32 = positionAfterPrecondition;
  }
  else
  {
    preconditionConstraintIsOk = (uint32_t)Len > (uint32_t)(uint16_t)5U;
    positionAfterPrecondition1 =
      EverParseCheckConstraintOk(preconditionConstraintIsOk,
        positionAfterPrecondition);
    if (EverParseIsError(positionAfterPrecondition1))
    {
      positionAfterSpecializedWrapper32 = positionAfterPrecondition1;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      hasBytes = 4ULL <= (InputLength - positionAfterPrecondition1);
      if (hasBytes)
      {
        positionAftertlv = positionAfterPrecondition1 + 4ULL;
      }
      else
      {
        positionAftertlv =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterPrecondition1);
      }
      if (EverParseIsError(positionAftertlv))
      {
        positionAfterSpecializedWrapper320 = positionAftertlv;
      }
      else
      {
        tlv = Load32Le(Input + (uint32_t)positionAfterPrecondition1);
        src64 = UlongToPtr(tlv);
        readOffset = 0ULL;
        writeOffset = 0ULL;
        failed = FALSE;
        ok = ProbeInit("___specialized_WRAPPER_32.tlv", (uint64_t)Len, Output);
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
          result =
            ValidateTlv((uint32_t)Len - (uint32_t)(uint16_t)5U,
              Ctxt,
              ErrorHandlerFn,
              EverParseStreamOf(Output),
              EverParseStreamLen(Output),
              0ULL);
          actionResult = !EverParseIsError(result);
        }
        else
        {
          ErrorHandlerFn("___specialized_WRAPPER_32",
            "tlv",
            EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
            EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
            Ctxt,
            Input,
            positionAfterPrecondition1);
          actionResult = FALSE;
        }
        if (actionResult)
        {
          positionAfterSpecializedWrapper320 = positionAftertlv;
        }
        else
        {
          positionAfterSpecializedWrapper320 =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
              positionAftertlv);
        }
      }
      if (EverParseIsSuccess(positionAfterSpecializedWrapper320))
      {
        positionAfterSpecializedWrapper32 = positionAfterSpecializedWrapper320;
      }
      else
      {
        ErrorHandlerFn("___specialized_WRAPPER_32",
          "tlv",
          EverParseErrorReasonOfResult(positionAfterSpecializedWrapper320),
          EverParseGetValidatorErrorKind(positionAfterSpecializedWrapper320),
          Ctxt,
          Input,
          positionAfterPrecondition1);
        positionAfterSpecializedWrapper32 = positionAfterSpecializedWrapper320;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterSpecializedWrapper32))
  {
    return positionAfterSpecializedWrapper32;
  }
  ErrorHandlerFn("___specialized_WRAPPER_32",
    "__precondition",
    EverParseErrorReasonOfResult(positionAfterSpecializedWrapper32),
    EverParseGetValidatorErrorKind(positionAfterSpecializedWrapper32),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterSpecializedWrapper32;
}

static void
EntryProbeWrapper0Tlv(
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
  ok = ProbeAndCopy(res1, rd, wr, Src, Dest);
  if (ok)
  {
    *ReadOffset = rd + res1;
    *WriteOffset = wr + res1;
    return;
  }
  *Failed = TRUE;
}

uint64_t
SpecializeDep1ValidateEntry(
  BOOLEAN Requestor32,
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
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
  uint64_t positionAfterEntry;
  uint64_t positionAfterEntry0;
  uint64_t positionAfterEntry1;
  if (Requestor32)
  {
    /* Validating field w32 */
    positionAfterEntry =
      ValidateSpecializedWrapper32(Len,
        Output,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterEntry))
    {
      return positionAfterEntry;
    }
    ErrorHandlerFn("_ENTRY",
      "w32",
      EverParseErrorReasonOfResult(positionAfterEntry),
      EverParseGetValidatorErrorKind(positionAfterEntry),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterEntry;
  }
  if (Requestor32 == FALSE)
  {
    /* Validating field w64 */
    positionAfterEntry0 =
      ValidateWrapper(EntryProbeWrapper0Tlv,
        Len,
        Output,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterEntry0))
    {
      return positionAfterEntry0;
    }
    ErrorHandlerFn("_ENTRY",
      "w64",
      EverParseErrorReasonOfResult(positionAfterEntry0),
      EverParseGetValidatorErrorKind(positionAfterEntry0),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterEntry0;
  }
  positionAfterEntry1 =
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
      StartPosition);
  if (EverParseIsSuccess(positionAfterEntry1))
  {
    return positionAfterEntry1;
  }
  ErrorHandlerFn("_ENTRY",
    "_x_14",
    EverParseErrorReasonOfResult(positionAfterEntry1),
    EverParseGetValidatorErrorKind(positionAfterEntry1),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterEntry1;
}

