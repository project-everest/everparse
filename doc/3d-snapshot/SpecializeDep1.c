

#include "SpecializeDep1.h"

#include "SpecializeDep1_ExternalAPI.h"
#include "EverParse.h"

static inline uint64_t
ValidateUnion(
  uint8_t Tag,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes0;
  uint64_t positionAfterCase0;
  BOOLEAN hasBytes1;
  uint64_t positionAfterCase1;
  BOOLEAN hasBytes;
  uint64_t positionAfterOther;
  if (Tag == 0U)
  {
    /* Validating field case0 */
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    hasBytes0 = (InputLen - StartPosition) >= 1ULL;
    if (hasBytes0)
    {
      positionAfterCase0 = StartPosition + 1ULL;
    }
    else
    {
      positionAfterCase0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterCase0))
    {
      return positionAfterCase0;
    }
    ErrorHandlerFn("_UNION",
      "case0",
      EverParseErrorReasonOfResult(positionAfterCase0),
      EverParseGetValidatorErrorKind(positionAfterCase0),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterCase0;
  }
  if (Tag == 1U)
  {
    /* Validating field case1 */
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    hasBytes1 = (InputLen - StartPosition) >= 2ULL;
    if (hasBytes1)
    {
      positionAfterCase1 = StartPosition + 2ULL;
    }
    else
    {
      positionAfterCase1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterCase1))
    {
      return positionAfterCase1;
    }
    ErrorHandlerFn("_UNION",
      "case1",
      EverParseErrorReasonOfResult(positionAfterCase1),
      EverParseGetValidatorErrorKind(positionAfterCase1),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterCase1;
  }
  /* Validating field other */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLen - StartPosition) >= 4ULL;
  if (hasBytes)
  {
    positionAfterOther = StartPosition + 4ULL;
  }
  else
  {
    positionAfterOther =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterOther))
  {
    return positionAfterOther;
  }
  ErrorHandlerFn("_UNION",
    "other",
    EverParseErrorReasonOfResult(positionAfterOther),
    EverParseGetValidatorErrorKind(positionAfterOther),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterOther;
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
  EVERPARSE_ERROR_HANDLER Err,
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
  if (Tag == 0U)
  {
    CopyBytes(1ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
    hasFailed = *Failed;
    if (hasFailed)
    {
      Err(Tn, Fn, "case0", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  else if (Tag == 1U)
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
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 1ULL;
  uint64_t positionAfterTag0;
  uint64_t positionAfterTag;
  uint8_t tag;
  BOOLEAN hasBytes;
  uint64_t positionAfterLength0;
  uint64_t positionAfterLength;
  uint32_t length;
  BOOLEAN lengthConstraintIsOk;
  uint64_t positionAfterCheckedLength;
  BOOLEAN hasEnoughBytes;
  uint64_t positionAfterPayload;
  uint8_t *truncatedInput;
  uint64_t truncatedInputLength;
  uint64_t result;
  uint64_t position;
  BOOLEAN ite;
  uint64_t positionAfterPayload_element;
  uint64_t result1;
  uint64_t res;
  if (hasBytes0)
  {
    positionAfterTag0 = StartPosition + 1ULL;
  }
  else
  {
    positionAfterTag0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterTag0))
  {
    positionAfterTag = positionAfterTag0;
  }
  else
  {
    ErrorHandlerFn("_TLV",
      "tag",
      EverParseErrorReasonOfResult(positionAfterTag0),
      EverParseGetValidatorErrorKind(positionAfterTag0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterTag = positionAfterTag0;
  }
  if (EverParseIsError(positionAfterTag))
  {
    return positionAfterTag;
  }
  tag = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterTag) >= 4ULL;
  if (hasBytes)
  {
    positionAfterLength0 = positionAfterTag + 4ULL;
  }
  else
  {
    positionAfterLength0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTag);
  }
  if (EverParseIsError(positionAfterLength0))
  {
    positionAfterLength = positionAfterLength0;
  }
  else
  {
    length = Load32Le(Input + (uint32_t)positionAfterTag);
    lengthConstraintIsOk = length == (uint32_t)Len;
    positionAfterCheckedLength =
      EverParseCheckConstraintOk(lengthConstraintIsOk,
        positionAfterLength0);
    if (EverParseIsError(positionAfterCheckedLength))
    {
      positionAfterLength = positionAfterCheckedLength;
    }
    else
    {
      /* Validating field payload */
      hasEnoughBytes = (InputLength - positionAfterCheckedLength) >= (uint64_t)(uint32_t)Len;
      if (!hasEnoughBytes)
      {
        positionAfterPayload =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedLength);
      }
      else
      {
        truncatedInput = Input;
        truncatedInputLength = positionAfterCheckedLength + (uint64_t)(uint32_t)Len;
        result = positionAfterCheckedLength;
        while (TRUE)
        {
          position = result;
          if (!((truncatedInputLength - position) >= 1ULL))
          {
            ite = TRUE;
          }
          else
          {
            positionAfterPayload_element =
              ValidateUnion(tag,
                Ctxt,
                ErrorHandlerFn,
                truncatedInput,
                truncatedInputLength,
                position);
            if (EverParseIsSuccess(positionAfterPayload_element))
            {
              result1 = positionAfterPayload_element;
            }
            else
            {
              ErrorHandlerFn("_TLV",
                "payload.element",
                EverParseErrorReasonOfResult(positionAfterPayload_element),
                EverParseGetValidatorErrorKind(positionAfterPayload_element),
                Ctxt,
                truncatedInput,
                position);
              result1 = positionAfterPayload_element;
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
        positionAfterPayload = res;
      }
      if (EverParseIsSuccess(positionAfterPayload))
      {
        positionAfterLength = positionAfterPayload;
      }
      else
      {
        ErrorHandlerFn("_TLV",
          "payload",
          EverParseErrorReasonOfResult(positionAfterPayload),
          EverParseGetValidatorErrorKind(positionAfterPayload),
          Ctxt,
          Input,
          positionAfterCheckedLength);
        positionAfterLength = positionAfterPayload;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterLength))
  {
    return positionAfterLength;
  }
  ErrorHandlerFn("_TLV",
    "length",
    EverParseErrorReasonOfResult(positionAfterLength),
    EverParseGetValidatorErrorKind(positionAfterLength),
    Ctxt,
    Input,
    positionAfterTag);
  return positionAfterLength;
}

static void
Specialized32ProbeTlv(
  uint16_t Len,
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
    EVERPARSE_ERROR_HANDLER x5,
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
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  uint64_t positionAfterPrecondition = StartPosition;
  uint64_t positionAfterPrecondition0;
  BOOLEAN preconditionConstraintIsOk;
  uint64_t positionAfterCheckedPrecondition;
  BOOLEAN hasBytes;
  uint64_t positionAfterTlv0;
  uint64_t positionAfterTlv;
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
    positionAfterPrecondition0 = positionAfterPrecondition;
  }
  else
  {
    preconditionConstraintIsOk = Len > (uint16_t)5U;
    positionAfterCheckedPrecondition =
      EverParseCheckConstraintOk(preconditionConstraintIsOk,
        positionAfterPrecondition);
    if (EverParseIsError(positionAfterCheckedPrecondition))
    {
      positionAfterPrecondition0 = positionAfterCheckedPrecondition;
    }
    else
    {
      /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
      hasBytes = (InputLength - positionAfterCheckedPrecondition) >= 8ULL;
      if (hasBytes)
      {
        positionAfterTlv0 = positionAfterCheckedPrecondition + 8ULL;
      }
      else
      {
        positionAfterTlv0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedPrecondition);
      }
      if (EverParseIsError(positionAfterTlv0))
      {
        positionAfterTlv = positionAfterTlv0;
      }
      else
      {
        tlv = Load64Le(Input + (uint32_t)positionAfterCheckedPrecondition);
        src64 = tlv;
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
            positionAfterCheckedPrecondition);
          actionResult = FALSE;
        }
        if (actionResult)
        {
          positionAfterTlv = positionAfterTlv0;
        }
        else
        {
          positionAfterTlv =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
              positionAfterTlv0);
        }
      }
      if (EverParseIsSuccess(positionAfterTlv))
      {
        positionAfterPrecondition0 = positionAfterTlv;
      }
      else
      {
        ErrorHandlerFn("_WRAPPER",
          "tlv",
          EverParseErrorReasonOfResult(positionAfterTlv),
          EverParseGetValidatorErrorKind(positionAfterTlv),
          Ctxt,
          Input,
          positionAfterCheckedPrecondition);
        positionAfterPrecondition0 = positionAfterTlv;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterPrecondition0))
  {
    return positionAfterPrecondition0;
  }
  ErrorHandlerFn("_WRAPPER",
    "__precondition",
    EverParseErrorReasonOfResult(positionAfterPrecondition0),
    EverParseGetValidatorErrorKind(positionAfterPrecondition0),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPrecondition0;
}

static inline uint64_t
ValidateSpecializedWrapper32(
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  uint64_t positionAfterPrecondition = StartPosition;
  uint64_t positionAfterPrecondition0;
  BOOLEAN preconditionConstraintIsOk;
  uint64_t positionAfterCheckedPrecondition;
  BOOLEAN hasBytes;
  uint64_t positionAfterTlv0;
  uint64_t positionAfterTlv;
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
    positionAfterPrecondition0 = positionAfterPrecondition;
  }
  else
  {
    preconditionConstraintIsOk = Len > (uint16_t)5U;
    positionAfterCheckedPrecondition =
      EverParseCheckConstraintOk(preconditionConstraintIsOk,
        positionAfterPrecondition);
    if (EverParseIsError(positionAfterCheckedPrecondition))
    {
      positionAfterPrecondition0 = positionAfterCheckedPrecondition;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      hasBytes = (InputLength - positionAfterCheckedPrecondition) >= 4ULL;
      if (hasBytes)
      {
        positionAfterTlv0 = positionAfterCheckedPrecondition + 4ULL;
      }
      else
      {
        positionAfterTlv0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedPrecondition);
      }
      if (EverParseIsError(positionAfterTlv0))
      {
        positionAfterTlv = positionAfterTlv0;
      }
      else
      {
        tlv = Load32Le(Input + (uint32_t)positionAfterCheckedPrecondition);
        src64 = UlongToPtr(tlv);
        readOffset = 0ULL;
        writeOffset = 0ULL;
        failed = FALSE;
        ok = ProbeInit("___specialized_WRAPPER_32.tlv", (uint64_t)(uint32_t)Len, Output);
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
            positionAfterCheckedPrecondition);
          actionResult = FALSE;
        }
        if (actionResult)
        {
          positionAfterTlv = positionAfterTlv0;
        }
        else
        {
          positionAfterTlv =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
              positionAfterTlv0);
        }
      }
      if (EverParseIsSuccess(positionAfterTlv))
      {
        positionAfterPrecondition0 = positionAfterTlv;
      }
      else
      {
        ErrorHandlerFn("___specialized_WRAPPER_32",
          "tlv",
          EverParseErrorReasonOfResult(positionAfterTlv),
          EverParseGetValidatorErrorKind(positionAfterTlv),
          Ctxt,
          Input,
          positionAfterCheckedPrecondition);
        positionAfterPrecondition0 = positionAfterTlv;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterPrecondition0))
  {
    return positionAfterPrecondition0;
  }
  ErrorHandlerFn("___specialized_WRAPPER_32",
    "__precondition",
    EverParseErrorReasonOfResult(positionAfterPrecondition0),
    EverParseGetValidatorErrorKind(positionAfterPrecondition0),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPrecondition0;
}

static void
EntryProbeWrapper0Tlv(
  uint16_t Arg0,
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
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  uint64_t positionAfterW32;
  uint64_t positionAfterW64;
  uint64_t positionAfterX14;
  if (Requestor32)
  {
    /* Validating field w32 */
    positionAfterW32 =
      ValidateSpecializedWrapper32(Len,
        Output,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterW32))
    {
      return positionAfterW32;
    }
    ErrorHandlerFn("_ENTRY",
      "w32",
      EverParseErrorReasonOfResult(positionAfterW32),
      EverParseGetValidatorErrorKind(positionAfterW32),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterW32;
  }
  if (Requestor32 == FALSE)
  {
    /* Validating field w64 */
    positionAfterW64 =
      ValidateWrapper(EntryProbeWrapper0Tlv,
        Len,
        Output,
        Ctxt,
        ErrorHandlerFn,
        Input,
        InputLen,
        StartPosition);
    if (EverParseIsSuccess(positionAfterW64))
    {
      return positionAfterW64;
    }
    ErrorHandlerFn("_ENTRY",
      "w64",
      EverParseErrorReasonOfResult(positionAfterW64),
      EverParseGetValidatorErrorKind(positionAfterW64),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterW64;
  }
  positionAfterX14 =
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
      StartPosition);
  if (EverParseIsSuccess(positionAfterX14))
  {
    return positionAfterX14;
  }
  ErrorHandlerFn("_ENTRY",
    "_x_14",
    EverParseErrorReasonOfResult(positionAfterX14),
    EverParseGetValidatorErrorKind(positionAfterX14),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX14;
}

