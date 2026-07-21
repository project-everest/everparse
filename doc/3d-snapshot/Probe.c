

#include "Probe.h"

#include "Probe_ExternalAPI.h"

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
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength - StartPosition);
  uint64_t positionAfterx;
  if (hasBytes0)
  {
    positionAfterx = StartPosition + 2ULL;
  }
  else
  {
    positionAfterx =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterT;
  if (EverParseIsError(positionAfterx))
  {
    positionAfterT = positionAfterx;
  }
  else
  {
    uint16_t r0 = Load16Le(Input + (uint32_t)StartPosition);
    uint16_t x = (uint16_t)(uint32_t)r0;
    BOOLEAN xConstraintIsOk = (uint32_t)x >= Bound;
    uint64_t positionAfterx1 = EverParseCheckConstraintOk(xConstraintIsOk, positionAfterx);
    if (EverParseIsError(positionAfterx1))
    {
      positionAfterT = positionAfterx1;
    }
    else
    {
      /* Validating field y */
      /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
      BOOLEAN hasBytes = 2ULL <= (InputLength - positionAfterx1);
      uint64_t positionAftery_refinement;
      if (hasBytes)
      {
        positionAftery_refinement = positionAfterx1 + 2ULL;
      }
      else
      {
        positionAftery_refinement =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterx1);
      }
      uint64_t positionAfterT0;
      if (EverParseIsError(positionAftery_refinement))
      {
        positionAfterT0 = positionAftery_refinement;
      }
      else
      {
        /* reading field_value */
        uint16_t r = Load16Le(Input + (uint32_t)positionAfterx1);
        uint16_t y_refinement = (uint16_t)(uint32_t)r;
        /* start: checking constraint */
        BOOLEAN y_refinementConstraintIsOk = y_refinement >= x;
        /* end: checking constraint */
        positionAfterT0 =
          EverParseCheckConstraintOk(y_refinementConstraintIsOk,
            positionAftery_refinement);
      }
      if (EverParseIsSuccess(positionAfterT0))
      {
        positionAfterT = positionAfterT0;
      }
      else
      {
        ErrorHandlerFn("_T",
          "y.refinement",
          EverParseErrorReasonOfResult(positionAfterT0),
          EverParseGetValidatorErrorKind(positionAfterT0),
          Ctxt,
          Input,
          positionAfterx1);
        positionAfterT = positionAfterT0;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterT))
  {
    return positionAfterT;
  }
  ErrorHandlerFn("_T",
    "x",
    EverParseErrorReasonOfResult(positionAfterT),
    EverParseGetValidatorErrorKind(positionAfterT),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterT;
}

uint64_t
ProbeValidateS(
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
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = 1ULL <= (InputLength - StartPosition);
  uint64_t positionAfterS;
  if (hasBytes0)
  {
    positionAfterS = StartPosition + 1ULL;
  }
  else
  {
    positionAfterS =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterbound;
  if (EverParseIsSuccess(positionAfterS))
  {
    positionAfterbound = positionAfterS;
  }
  else
  {
    ErrorHandlerFn("_S",
      "bound",
      EverParseErrorReasonOfResult(positionAfterS),
      EverParseGetValidatorErrorKind(positionAfterS),
      Ctxt,
      Input,
      StartPosition);
    positionAfterbound = positionAfterS;
  }
  if (EverParseIsError(positionAfterbound))
  {
    return positionAfterbound;
  }
  uint8_t bound = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - positionAfterbound);
  uint64_t positionAftertpointer;
  if (hasBytes)
  {
    positionAftertpointer = positionAfterbound + 8ULL;
  }
  else
  {
    positionAftertpointer =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterbound);
  }
  uint64_t positionAfterS0;
  if (EverParseIsError(positionAftertpointer))
  {
    positionAfterS0 = positionAftertpointer;
  }
  else
  {
    uint64_t tpointer = Load64Le(Input + (uint32_t)positionAfterbound);
    uint64_t src64 = tpointer;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_S.tpointer", (uint64_t)4U, Dest);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr, src64, Dest);
      if (ok1)
      {
        readOffset = rd + (uint64_t)4U;
        writeOffset = wr + (uint64_t)4U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_S", "tpointer", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
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
        ValidateT((uint32_t)bound,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(Dest),
          EverParseStreamLen(Dest),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_S",
        "tpointer",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAfterbound);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterS0 = positionAftertpointer;
    }
    else
    {
      positionAfterS0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftertpointer);
    }
  }
  if (EverParseIsSuccess(positionAfterS0))
  {
    return positionAfterS0;
  }
  ErrorHandlerFn("_S",
    "tpointer",
    EverParseErrorReasonOfResult(positionAfterS0),
    EverParseGetValidatorErrorKind(positionAfterS0),
    Ctxt,
    Input,
    positionAfterbound);
  return positionAfterS0;
}

uint64_t
ProbeValidateU(
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
  /* Validating field tag */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = 1ULL <= (InputLength - StartPosition);
  uint64_t positionAfterU;
  if (hasBytes0)
  {
    positionAfterU = StartPosition + 1ULL;
  }
  else
  {
    positionAfterU =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterU))
  {
    res = positionAfterU;
  }
  else
  {
    ErrorHandlerFn("_U",
      "tag",
      EverParseErrorReasonOfResult(positionAfterU),
      EverParseGetValidatorErrorKind(positionAfterU),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterU;
  }
  uint64_t positionAftertag = res;
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - positionAftertag);
  uint64_t positionAfterspointer;
  if (hasBytes)
  {
    positionAfterspointer = positionAftertag + 8ULL;
  }
  else
  {
    positionAfterspointer =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertag);
  }
  uint64_t positionAfterU0;
  if (EverParseIsError(positionAfterspointer))
  {
    positionAfterU0 = positionAfterspointer;
  }
  else
  {
    uint64_t spointer = Load64Le(Input + (uint32_t)positionAftertag);
    uint64_t src64 = spointer;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_U.spointer", (uint64_t)9U, DestS);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopy2((uint64_t)9U, rd, wr, src64, DestS);
      if (ok1)
      {
        readOffset = rd + (uint64_t)9U;
        writeOffset = wr + (uint64_t)9U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_U", "spointer", "probe", 0ULL, Ctxt, EverParseStreamOf(DestS), 0ULL);
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
        ProbeValidateS(DestT,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestS),
          EverParseStreamLen(DestS),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_U",
        "spointer",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAftertag);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterU0 = positionAfterspointer;
    }
    else
    {
      positionAfterU0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterspointer);
    }
  }
  if (EverParseIsSuccess(positionAfterU0))
  {
    return positionAfterU0;
  }
  ErrorHandlerFn("_U",
    "spointer",
    EverParseErrorReasonOfResult(positionAfterU0),
    EverParseGetValidatorErrorKind(positionAfterU0),
    Ctxt,
    Input,
    positionAftertag);
  return positionAfterU0;
}

uint64_t
ProbeValidateV(
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
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = 1ULL <= (InputLength - StartPosition);
  uint64_t positionAfterV;
  if (hasBytes0)
  {
    positionAfterV = StartPosition + 1ULL;
  }
  else
  {
    positionAfterV =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAftertag;
  if (EverParseIsSuccess(positionAfterV))
  {
    positionAftertag = positionAfterV;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tag",
      EverParseErrorReasonOfResult(positionAfterV),
      EverParseGetValidatorErrorKind(positionAfterV),
      Ctxt,
      Input,
      StartPosition);
    positionAftertag = positionAfterV;
  }
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  uint8_t tag = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes1 = 8ULL <= (InputLength - positionAftertag);
  uint64_t positionAftersptr0;
  if (hasBytes1)
  {
    positionAftersptr0 = positionAftertag + 8ULL;
  }
  else
  {
    positionAftersptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertag);
  }
  uint64_t positionAfterV0;
  if (EverParseIsError(positionAftersptr0))
  {
    positionAfterV0 = positionAftersptr0;
  }
  else
  {
    uint64_t sptr = Load64Le(Input + (uint32_t)positionAftertag);
    uint64_t src64 = sptr;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_V.sptr", (uint64_t)9U, DestS);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopy2((uint64_t)9U, rd, wr, src64, DestS);
      if (ok1)
      {
        readOffset = rd + (uint64_t)9U;
        writeOffset = wr + (uint64_t)9U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_V", "sptr", "probe", 0ULL, Ctxt, EverParseStreamOf(DestS), 0ULL);
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
        ProbeValidateS(DestT,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestS),
          EverParseStreamLen(DestS),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_V",
        "sptr",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAftertag);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterV0 = positionAftersptr0;
    }
    else
    {
      positionAfterV0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftersptr0);
    }
  }
  uint64_t positionAftersptr;
  if (EverParseIsSuccess(positionAfterV0))
  {
    positionAftersptr = positionAfterV0;
  }
  else
  {
    ErrorHandlerFn("_V",
      "sptr",
      EverParseErrorReasonOfResult(positionAfterV0),
      EverParseGetValidatorErrorKind(positionAfterV0),
      Ctxt,
      Input,
      positionAftertag);
    positionAftersptr = positionAfterV0;
  }
  if (EverParseIsError(positionAftersptr))
  {
    return positionAftersptr;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes2 = 8ULL <= (InputLength - positionAftersptr);
  uint64_t positionAftertptr0;
  if (hasBytes2)
  {
    positionAftertptr0 = positionAftersptr + 8ULL;
  }
  else
  {
    positionAftertptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftersptr);
  }
  uint64_t positionAfterV1;
  if (EverParseIsError(positionAftertptr0))
  {
    positionAfterV1 = positionAftertptr0;
  }
  else
  {
    uint64_t tptr = Load64Le(Input + (uint32_t)positionAftersptr);
    uint64_t src64 = tptr;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_V.tptr", (uint64_t)8U, DestT);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopy2((uint64_t)8U, rd, wr, src64, DestT);
      if (ok1)
      {
        readOffset = rd + (uint64_t)8U;
        writeOffset = wr + (uint64_t)8U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_V", "tptr", "probe", 0ULL, Ctxt, EverParseStreamOf(DestT), 0ULL);
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
        ValidateT((uint32_t)17U,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestT),
          EverParseStreamLen(DestT),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_V",
        "tptr",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAftersptr);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterV1 = positionAftertptr0;
    }
    else
    {
      positionAfterV1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftertptr0);
    }
  }
  uint64_t positionAftertptr;
  if (EverParseIsSuccess(positionAfterV1))
  {
    positionAftertptr = positionAfterV1;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tptr",
      EverParseErrorReasonOfResult(positionAfterV1),
      EverParseGetValidatorErrorKind(positionAfterV1),
      Ctxt,
      Input,
      positionAftersptr);
    positionAftertptr = positionAfterV1;
  }
  if (EverParseIsError(positionAftertptr))
  {
    return positionAftertptr;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - positionAftertptr);
  uint64_t positionAftert2ptr;
  if (hasBytes)
  {
    positionAftert2ptr = positionAftertptr + 8ULL;
  }
  else
  {
    positionAftert2ptr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertptr);
  }
  uint64_t positionAfterV2;
  if (EverParseIsError(positionAftert2ptr))
  {
    positionAfterV2 = positionAftert2ptr;
  }
  else
  {
    uint64_t t2ptr = Load64Le(Input + (uint32_t)positionAftertptr);
    uint64_t src64 = t2ptr;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_V.t2ptr", (uint64_t)8U, DestT);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopy2((uint64_t)8U, rd, wr, src64, DestT);
      if (ok1)
      {
        readOffset = rd + (uint64_t)8U;
        writeOffset = wr + (uint64_t)8U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_V", "t2ptr", "probe", 0ULL, Ctxt, EverParseStreamOf(DestT), 0ULL);
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
        ValidateT((uint32_t)tag,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestT),
          EverParseStreamLen(DestT),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_V",
        "t2ptr",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAftertptr);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterV2 = positionAftert2ptr;
    }
    else
    {
      positionAfterV2 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftert2ptr);
    }
  }
  if (EverParseIsSuccess(positionAfterV2))
  {
    return positionAfterV2;
  }
  ErrorHandlerFn("_V",
    "t2ptr",
    EverParseErrorReasonOfResult(positionAfterV2),
    EverParseGetValidatorErrorKind(positionAfterV2),
    Ctxt,
    Input,
    positionAftertptr);
  return positionAfterV2;
}

uint64_t
ProbeValidateIndirect(
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
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  BOOLEAN hasBytes = 9ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 9ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

static inline uint64_t ValidateTt(uint64_t InputLength, uint64_t StartPosition)
{
  BOOLEAN hasBytes = 9ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 9ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

uint64_t
ProbeValidateI(
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
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - StartPosition);
  uint64_t positionAfterttptr;
  if (hasBytes)
  {
    positionAfterttptr = StartPosition + 8ULL;
  }
  else
  {
    positionAfterttptr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterI;
  if (EverParseIsError(positionAfterttptr))
  {
    positionAfterI = positionAfterttptr;
  }
  else
  {
    uint64_t ttptr = Load64Le(Input + (uint32_t)StartPosition);
    uint64_t src64 = ttptr;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_I.ttptr", (uint64_t)9U, Dest);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopy2((uint64_t)9U, rd, wr, src64, Dest);
      if (ok1)
      {
        readOffset = rd + (uint64_t)9U;
        writeOffset = wr + (uint64_t)9U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_I", "ttptr", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    BOOLEAN actionResult;
    if (b != 0ULL)
    {
      uint8_t *unused = EverParseStreamOf(Dest);
      KRML_MAYBE_UNUSED_VAR(unused);
      uint64_t result = ValidateTt(EverParseStreamLen(Dest), 0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_I",
        "ttptr",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        StartPosition);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterI = positionAfterttptr;
    }
    else
    {
      positionAfterI =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterttptr);
    }
  }
  if (EverParseIsSuccess(positionAfterI))
  {
    return positionAfterI;
  }
  ErrorHandlerFn("_I",
    "ttptr",
    EverParseErrorReasonOfResult(positionAfterI),
    EverParseGetValidatorErrorKind(positionAfterI),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterI;
}

uint64_t
ProbeValidateMultiProbe(
  EVERPARSE_COPY_BUFFER_T DestT1,
  EVERPARSE_COPY_BUFFER_T DestT2,
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
  /* Validating field fst */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterMultiProbe;
  if (hasBytes0)
  {
    positionAfterMultiProbe = StartPosition + 4ULL;
  }
  else
  {
    positionAfterMultiProbe =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterMultiProbe))
  {
    res0 = positionAfterMultiProbe;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "fst",
      EverParseErrorReasonOfResult(positionAfterMultiProbe),
      EverParseGetValidatorErrorKind(positionAfterMultiProbe),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterMultiProbe;
  }
  uint64_t positionAfterfst = res0;
  if (EverParseIsError(positionAfterfst))
  {
    return positionAfterfst;
  }
  /* Validating field snd */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes1 = 4ULL <= (InputLength - positionAfterfst);
  uint64_t positionAfterMultiProbe0;
  if (hasBytes1)
  {
    positionAfterMultiProbe0 = positionAfterfst + 4ULL;
  }
  else
  {
    positionAfterMultiProbe0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterfst);
  }
  uint64_t res1;
  if (EverParseIsSuccess(positionAfterMultiProbe0))
  {
    res1 = positionAfterMultiProbe0;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "snd",
      EverParseErrorReasonOfResult(positionAfterMultiProbe0),
      EverParseGetValidatorErrorKind(positionAfterMultiProbe0),
      Ctxt,
      Input,
      positionAfterfst);
    res1 = positionAfterMultiProbe0;
  }
  uint64_t positionAftersnd = res1;
  if (EverParseIsError(positionAftersnd))
  {
    return positionAftersnd;
  }
  /* Validating field tag */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes2 = 1ULL <= (InputLength - positionAftersnd);
  uint64_t positionAfterMultiProbe1;
  if (hasBytes2)
  {
    positionAfterMultiProbe1 = positionAftersnd + 1ULL;
  }
  else
  {
    positionAfterMultiProbe1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftersnd);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterMultiProbe1))
  {
    res = positionAfterMultiProbe1;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "tag",
      EverParseErrorReasonOfResult(positionAfterMultiProbe1),
      EverParseGetValidatorErrorKind(positionAfterMultiProbe1),
      Ctxt,
      Input,
      positionAftersnd);
    res = positionAfterMultiProbe1;
  }
  uint64_t positionAftertag = res;
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes3 = 8ULL <= (InputLength - positionAftertag);
  uint64_t positionAftertptr10;
  if (hasBytes3)
  {
    positionAftertptr10 = positionAftertag + 8ULL;
  }
  else
  {
    positionAftertptr10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertag);
  }
  uint64_t positionAfterMultiProbe2;
  if (EverParseIsError(positionAftertptr10))
  {
    positionAfterMultiProbe2 = positionAftertptr10;
  }
  else
  {
    uint64_t tptr1 = Load64Le(Input + (uint32_t)positionAftertag);
    uint64_t src64 = tptr1;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_MultiProbe.tptr1", (uint64_t)4U, DestT1);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr, src64, DestT1);
      if (ok1)
      {
        readOffset = rd + (uint64_t)4U;
        writeOffset = wr + (uint64_t)4U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_MultiProbe", "tptr1", "probe", 0ULL, Ctxt, EverParseStreamOf(DestT1), 0ULL);
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
        ValidateT((uint32_t)17U,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestT1),
          EverParseStreamLen(DestT1),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_MultiProbe",
        "tptr1",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAftertag);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterMultiProbe2 = positionAftertptr10;
    }
    else
    {
      positionAfterMultiProbe2 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftertptr10);
    }
  }
  uint64_t positionAftertptr1;
  if (EverParseIsSuccess(positionAfterMultiProbe2))
  {
    positionAftertptr1 = positionAfterMultiProbe2;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "tptr1",
      EverParseErrorReasonOfResult(positionAfterMultiProbe2),
      EverParseGetValidatorErrorKind(positionAfterMultiProbe2),
      Ctxt,
      Input,
      positionAftertag);
    positionAftertptr1 = positionAfterMultiProbe2;
  }
  if (EverParseIsError(positionAftertptr1))
  {
    return positionAftertptr1;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - positionAftertptr1);
  uint64_t positionAftertptr2;
  if (hasBytes)
  {
    positionAftertptr2 = positionAftertptr1 + 8ULL;
  }
  else
  {
    positionAftertptr2 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertptr1);
  }
  uint64_t positionAfterMultiProbe3;
  if (EverParseIsError(positionAftertptr2))
  {
    positionAfterMultiProbe3 = positionAftertptr2;
  }
  else
  {
    uint64_t tptr2 = Load64Le(Input + (uint32_t)positionAftertptr1);
    uint64_t src64 = tptr2;
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_MultiProbe.tptr2", (uint64_t)4U, DestT2);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopyAlt((uint64_t)4U, rd, wr, src64, DestT2);
      if (ok1)
      {
        readOffset = rd + (uint64_t)4U;
        writeOffset = wr + (uint64_t)4U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_MultiProbe", "tptr2", "probe", 0ULL, Ctxt, EverParseStreamOf(DestT2), 0ULL);
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
        ValidateT((uint32_t)42U,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestT2),
          EverParseStreamLen(DestT2),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_MultiProbe",
        "tptr2",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAftertptr1);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterMultiProbe3 = positionAftertptr2;
    }
    else
    {
      positionAfterMultiProbe3 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftertptr2);
    }
  }
  if (EverParseIsSuccess(positionAfterMultiProbe3))
  {
    return positionAfterMultiProbe3;
  }
  ErrorHandlerFn("_MultiProbe",
    "tptr2",
    EverParseErrorReasonOfResult(positionAfterMultiProbe3),
    EverParseGetValidatorErrorKind(positionAfterMultiProbe3),
    Ctxt,
    Input,
    positionAftertptr1);
  return positionAfterMultiProbe3;
}

uint64_t
ProbeValidateMaybeT(
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
  uint64_t positionAfterMaybeT;
  if (hasBytes0)
  {
    positionAfterMaybeT = StartPosition + 4ULL;
  }
  else
  {
    positionAfterMaybeT =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterBound;
  if (EverParseIsSuccess(positionAfterMaybeT))
  {
    positionAfterBound = positionAfterMaybeT;
  }
  else
  {
    ErrorHandlerFn("_MaybeT",
      "Bound",
      EverParseErrorReasonOfResult(positionAfterMaybeT),
      EverParseGetValidatorErrorKind(positionAfterMaybeT),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBound = positionAfterMaybeT;
  }
  if (EverParseIsError(positionAfterBound))
  {
    return positionAfterBound;
  }
  uint32_t bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = 8ULL <= (InputLength - positionAfterBound);
  uint64_t positionAfterptr;
  if (hasBytes)
  {
    positionAfterptr = positionAfterBound + 8ULL;
  }
  else
  {
    positionAfterptr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  uint64_t positionAfterMaybeT0;
  if (EverParseIsError(positionAfterptr))
  {
    positionAfterMaybeT0 = positionAfterptr;
  }
  else
  {
    uint64_t ptr = Load64Le(Input + (uint32_t)positionAfterBound);
    uint64_t src64 = ptr;
    BOOLEAN actionResult;
    if (src64 == 0ULL)
    {
      actionResult = TRUE;
    }
    else
    {
      uint64_t readOffset = 0ULL;
      uint64_t writeOffset = 0ULL;
      BOOLEAN failed = FALSE;
      BOOLEAN ok = ProbeInit2("_MaybeT.ptr", (uint64_t)4U, Dest);
      if (ok)
      {
        uint64_t rd = readOffset;
        uint64_t wr = writeOffset;
        BOOLEAN ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr, src64, Dest);
        if (ok1)
        {
          readOffset = rd + (uint64_t)4U;
          writeOffset = wr + (uint64_t)4U;
        }
        else
        {
          failed = TRUE;
        }
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
        ErrorHandlerFn("_MaybeT", "ptr", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
        b = 0ULL;
      }
      else
      {
        b = wr;
      }
      if (b != 0ULL)
      {
        uint64_t
        result =
          ValidateT(bound,
            Ctxt,
            ErrorHandlerFn,
            EverParseStreamOf(Dest),
            EverParseStreamLen(Dest),
            0ULL);
        actionResult = !EverParseIsError(result);
      }
      else
      {
        ErrorHandlerFn("_MaybeT",
          "ptr",
          EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
          EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
          Ctxt,
          Input,
          positionAfterBound);
        actionResult = FALSE;
      }
    }
    if (actionResult)
    {
      positionAfterMaybeT0 = positionAfterptr;
    }
    else
    {
      positionAfterMaybeT0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptr);
    }
  }
  if (EverParseIsSuccess(positionAfterMaybeT0))
  {
    return positionAfterMaybeT0;
  }
  ErrorHandlerFn("_MaybeT",
    "ptr",
    EverParseErrorReasonOfResult(positionAfterMaybeT0),
    EverParseGetValidatorErrorKind(positionAfterMaybeT0),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterMaybeT0;
}

uint64_t
ProbeValidateCoercePtr(
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
  uint64_t positionAfterCoercePtr;
  if (hasBytes0)
  {
    positionAfterCoercePtr = StartPosition + 4ULL;
  }
  else
  {
    positionAfterCoercePtr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterBound;
  if (EverParseIsSuccess(positionAfterCoercePtr))
  {
    positionAfterBound = positionAfterCoercePtr;
  }
  else
  {
    ErrorHandlerFn("_CoercePtr",
      "Bound",
      EverParseErrorReasonOfResult(positionAfterCoercePtr),
      EverParseGetValidatorErrorKind(positionAfterCoercePtr),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBound = positionAfterCoercePtr;
  }
  if (EverParseIsError(positionAfterBound))
  {
    return positionAfterBound;
  }
  uint32_t bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = 4ULL <= (InputLength - positionAfterBound);
  uint64_t positionAfterptr;
  if (hasBytes)
  {
    positionAfterptr = positionAfterBound + 4ULL;
  }
  else
  {
    positionAfterptr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  uint64_t positionAfterCoercePtr0;
  if (EverParseIsError(positionAfterptr))
  {
    positionAfterCoercePtr0 = positionAfterptr;
  }
  else
  {
    uint32_t ptr = Load32Le(Input + (uint32_t)positionAfterBound);
    uint64_t src64 = UlongToPtr2(ptr);
    uint64_t readOffset = 0ULL;
    uint64_t writeOffset = 0ULL;
    BOOLEAN failed = FALSE;
    BOOLEAN ok = ProbeInit2("_CoercePtr.ptr", (uint64_t)4U, Dest);
    if (ok)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      BOOLEAN ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr, src64, Dest);
      if (ok1)
      {
        readOffset = rd + (uint64_t)4U;
        writeOffset = wr + (uint64_t)4U;
      }
      else
      {
        failed = TRUE;
      }
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
      ErrorHandlerFn("_CoercePtr", "ptr", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
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
        ValidateT(bound,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(Dest),
          EverParseStreamLen(Dest),
          0ULL);
      actionResult = !EverParseIsError(result);
    }
    else
    {
      ErrorHandlerFn("_CoercePtr",
        "ptr",
        EverParseErrorReasonOfResult(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        EverParseGetValidatorErrorKind(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED),
        Ctxt,
        Input,
        positionAfterBound);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterCoercePtr0 = positionAfterptr;
    }
    else
    {
      positionAfterCoercePtr0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptr);
    }
  }
  if (EverParseIsSuccess(positionAfterCoercePtr0))
  {
    return positionAfterCoercePtr0;
  }
  ErrorHandlerFn("_CoercePtr",
    "ptr",
    EverParseErrorReasonOfResult(positionAfterCoercePtr0),
    EverParseGetValidatorErrorKind(positionAfterCoercePtr0),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterCoercePtr0;
}

