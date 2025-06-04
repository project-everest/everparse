

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
  if (Tag == 0U)
  {
    /* Validating field case0 */
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    BOOLEAN hasBytes = 1ULL <= (InputLen - StartPosition);
    uint64_t positionAfterUnion;
    if (hasBytes)
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
  if (Tag == 1U)
  {
    /* Validating field case1 */
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    BOOLEAN hasBytes = 2ULL <= (InputLen - StartPosition);
    uint64_t positionAfterUnion;
    if (hasBytes)
    {
      positionAfterUnion = StartPosition + 2ULL;
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
      "case1",
      EverParseErrorReasonOfResult(positionAfterUnion),
      EverParseGetValidatorErrorKind(positionAfterUnion),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterUnion;
  }
  /* Validating field other */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = 4ULL <= (InputLen - StartPosition);
  uint64_t positionAfterUnion;
  if (hasBytes)
  {
    positionAfterUnion = StartPosition + 4ULL;
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
    "other",
    EverParseErrorReasonOfResult(positionAfterUnion),
    EverParseGetValidatorErrorKind(positionAfterUnion),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterUnion;
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
  if (Tag == 0U)
  {
    CopyBytes(1ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
    BOOLEAN hasFailed = *Failed;
    if (hasFailed)
    {
      Err(Tn, Fn, "case0", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  else if (Tag == 1U)
  {
    CopyBytes(2ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
    BOOLEAN hasFailed = *Failed;
    if (hasFailed)
    {
      Err(Tn, Fn, "case1", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  else
  {
    CopyBytes(4ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
    BOOLEAN hasFailed = *Failed;
    if (hasFailed)
    {
      Err(Tn, Fn, "other", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
  }
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "field", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
}

static inline uint64_t
ValidateTlv(
  uint8_t Expected,
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
  uint64_t positionAftertag;
  if (hasBytes0)
  {
    positionAftertag = StartPosition + 1ULL;
  }
  else
  {
    positionAftertag =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterTlv;
  if (EverParseIsError(positionAftertag))
  {
    positionAfterTlv = positionAftertag;
  }
  else
  {
    uint8_t tag = Input[(uint32_t)StartPosition];
    BOOLEAN tagConstraintIsOk = tag == Expected;
    uint64_t positionAftertag1 = EverParseCheckConstraintOk(tagConstraintIsOk, positionAftertag);
    if (EverParseIsError(positionAftertag1))
    {
      positionAfterTlv = positionAftertag1;
    }
    else
    {
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      BOOLEAN hasBytes = 4ULL <= (InputLength - positionAftertag1);
      uint64_t positionAfterlength;
      if (hasBytes)
      {
        positionAfterlength = positionAftertag1 + 4ULL;
      }
      else
      {
        positionAfterlength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAftertag1);
      }
      uint64_t positionAfterTlv0;
      if (EverParseIsError(positionAfterlength))
      {
        positionAfterTlv0 = positionAfterlength;
      }
      else
      {
        uint32_t length = Load32Le(Input + (uint32_t)positionAftertag1);
        BOOLEAN lengthConstraintIsOk = length == (uint32_t)Len;
        uint64_t
        positionAfterlength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterlength);
        if (EverParseIsError(positionAfterlength1))
        {
          positionAfterTlv0 = positionAfterlength1;
        }
        else
        {
          /* Validating field payload */
          BOOLEAN hasEnoughBytes = (uint64_t)(uint32_t)Len <= (InputLength - positionAfterlength1);
          uint64_t positionAfterTlv1;
          if (!hasEnoughBytes)
          {
            positionAfterTlv1 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterlength1);
          }
          else
          {
            uint8_t *truncatedInput = Input;
            uint64_t truncatedInputLength = positionAfterlength1 + (uint64_t)(uint32_t)Len;
            uint64_t result = positionAfterlength1;
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
                positionAfterTlv2 =
                  ValidateUnion(Expected,
                    Ctxt,
                    ErrorHandlerFn,
                    truncatedInput,
                    truncatedInputLength,
                    position);
                uint64_t result1;
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
            uint64_t res = result;
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
        positionAfterTlv = positionAfterTlv0;
      }
      else
      {
        ErrorHandlerFn("_TLV",
          "length",
          EverParseErrorReasonOfResult(positionAfterTlv0),
          EverParseGetValidatorErrorKind(positionAfterTlv0),
          Ctxt,
          Input,
          positionAftertag1);
        positionAfterTlv = positionAfterTlv0;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterTlv))
  {
    return positionAfterTlv;
  }
  ErrorHandlerFn("_TLV",
    "tag",
    EverParseErrorReasonOfResult(positionAfterTlv),
    EverParseGetValidatorErrorKind(positionAfterTlv),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTlv;
}

static void
Specialized32ProbeTlv(
  uint8_t Expected,
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
  CopyBytes(5ULL, ReadOffset, WriteOffset, Failed, Src, Dest);
  BOOLEAN hasFailed = *Failed;
  if (hasFailed)
  {
    Err(Tn, Fn, "tag", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    return;
  }
  uint64_t ctr = (uint64_t)(uint32_t)Len;
  uint64_t c0 = ctr;
  BOOLEAN hasFailed1 = *Failed;
  BOOLEAN cond = c0 != 0ULL && !hasFailed1;
  while (cond)
  {
    uint64_t r0 = *ReadOffset;
    Specialized32ProbeUnion(Expected,
      Tn,
      Fn,
      Ctxt,
      Err,
      ReadOffset,
      WriteOffset,
      Failed,
      Src,
      Dest);
    BOOLEAN hasFailed10 = *Failed;
    if (hasFailed10)
    {
      Err(Tn, Fn, "payload", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
    }
    BOOLEAN hasFailed11 = *Failed;
    uint64_t r1 = *ReadOffset;
    uint64_t bytesRead = r1 - r0;
    uint64_t c = ctr;
    if (hasFailed11 || bytesRead == 0ULL || c < bytesRead)
    {
      Err(Tn, Fn, Det, 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      *Failed = TRUE;
    }
    else
    {
      ctr = c - bytesRead;
    }
    uint64_t c1 = ctr;
    BOOLEAN hasFailed12 = *Failed;
    cond = c1 != 0ULL && !hasFailed12;
  }
}

static inline uint64_t
ValidateWrapper(
  void
  (*ProbeTlv)(
    uint8_t x0,
    uint16_t x1,
    EVERPARSE_STRING x2,
    EVERPARSE_STRING x3,
    EVERPARSE_STRING x4,
    uint8_t *x5,
    void
    (*x6)(
      EVERPARSE_STRING x0,
      EVERPARSE_STRING x1,
      EVERPARSE_STRING x2,
      uint64_t x3,
      uint8_t *x4,
      uint8_t *x5,
      uint64_t x6
    ),
    uint64_t *x7,
    uint64_t *x8,
    BOOLEAN *x9,
    uint64_t x10,
    uint64_t x11,
    EVERPARSE_COPY_BUFFER_T x12
  ),
  uint8_t Expected,
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
  if (EverParseIsError(positionAfterPrecondition))
  {
    positionAfterWrapper = positionAfterPrecondition;
  }
  else
  {
    BOOLEAN preconditionConstraintIsOk = Len > (uint16_t)5U;
    uint64_t
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
      BOOLEAN hasBytes = 8ULL <= (InputLength - positionAfterPrecondition1);
      uint64_t positionAftertlv;
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
      uint64_t positionAfterWrapper0;
      if (EverParseIsError(positionAftertlv))
      {
        positionAfterWrapper0 = positionAftertlv;
      }
      else
      {
        uint64_t tlv = Load64Le(Input + (uint32_t)positionAfterPrecondition1);
        uint64_t src64 = tlv;
        uint64_t readOffset = 0ULL;
        uint64_t writeOffset = 0ULL;
        BOOLEAN failed = FALSE;
        BOOLEAN ok = ProbeInit((uint64_t)Len, Output);
        if (ok)
        {
          ProbeTlv(Expected,
            (uint32_t)Len - (uint32_t)(uint16_t)5U,
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
        uint64_t wr = writeOffset;
        BOOLEAN hasFailed = failed;
        uint64_t b;
        if (hasFailed)
        {
          ErrorHandlerFn("_WRAPPER", "tlv", "probe", 0ULL, Ctxt, EverParseStreamOf(Output), 0ULL);
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
            ValidateTlv(Expected,
              (uint32_t)Len - (uint32_t)(uint16_t)5U,
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
  uint8_t Expected,
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
  if (EverParseIsError(positionAfterPrecondition))
  {
    positionAfterSpecializedWrapper32 = positionAfterPrecondition;
  }
  else
  {
    BOOLEAN preconditionConstraintIsOk = Len > (uint16_t)5U;
    uint64_t
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
      BOOLEAN hasBytes = 4ULL <= (InputLength - positionAfterPrecondition1);
      uint64_t positionAftertlv;
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
      uint64_t positionAfterSpecializedWrapper320;
      if (EverParseIsError(positionAftertlv))
      {
        positionAfterSpecializedWrapper320 = positionAftertlv;
      }
      else
      {
        uint32_t tlv = Load32Le(Input + (uint32_t)positionAfterPrecondition1);
        uint64_t src64 = UlongToPtr(tlv);
        uint64_t readOffset = 0ULL;
        uint64_t writeOffset = 0ULL;
        BOOLEAN failed = FALSE;
        BOOLEAN ok = ProbeInit((uint64_t)Len, Output);
        if (ok)
        {
          Specialized32ProbeTlv(Expected,
            (uint32_t)Len - (uint32_t)(uint16_t)5U,
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
        uint64_t wr = writeOffset;
        BOOLEAN hasFailed = failed;
        uint64_t b;
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
        BOOLEAN actionResult;
        if (b != 0ULL)
        {
          uint64_t
          result =
            ValidateTlv(Expected,
              (uint32_t)Len - (uint32_t)(uint16_t)5U,
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
  uint8_t Arg0,
  uint16_t Arg1,
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
  KRML_MAYBE_UNUSED_VAR(Arg1);
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
SpecializeDep1ValidateEntry(
  BOOLEAN Requestor32,
  uint8_t Expected,
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
  if (Requestor32)
  {
    /* Validating field w32 */
    uint64_t
    positionAfterEntry =
      ValidateSpecializedWrapper32(Expected,
        Len,
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
    uint64_t
    positionAfterEntry =
      ValidateWrapper(EntryProbeWrapper0Tlv,
        Expected,
        Len,
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
      "w64",
      EverParseErrorReasonOfResult(positionAfterEntry),
      EverParseGetValidatorErrorKind(positionAfterEntry),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterEntry;
  }
  uint64_t
  positionAfterEntry =
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
      StartPosition);
  if (EverParseIsSuccess(positionAfterEntry))
  {
    return positionAfterEntry;
  }
  ErrorHandlerFn("_ENTRY",
    "_x_14",
    EverParseErrorReasonOfResult(positionAfterEntry),
    EverParseGetValidatorErrorKind(positionAfterEntry),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterEntry;
}

