

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
  uint64_t positionAfterT;
  uint16_t r0;
  uint16_t x;
  BOOLEAN xConstraintIsOk;
  uint64_t positionAfterx1;
  BOOLEAN hasBytes;
  uint64_t positionAftery_refinement;
  uint64_t positionAfterT0;
  uint16_t r;
  uint16_t y_refinement;
  BOOLEAN y_refinementConstraintIsOk;
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
  if (EverParseIsError(positionAfterx))
  {
    positionAfterT = positionAfterx;
  }
  else
  {
    r0 = Load16Le(Input + (uint32_t)StartPosition);
    x = (uint16_t)(uint32_t)r0;
    xConstraintIsOk = (uint32_t)x >= Bound;
    positionAfterx1 = EverParseCheckConstraintOk(xConstraintIsOk, positionAfterx);
    if (EverParseIsError(positionAfterx1))
    {
      positionAfterT = positionAfterx1;
    }
    else
    {
      /* Validating field y */
      /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
      hasBytes = 2ULL <= (InputLength - positionAfterx1);
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
      if (EverParseIsError(positionAftery_refinement))
      {
        positionAfterT0 = positionAftery_refinement;
      }
      else
      {
        /* reading field_value */
        r = Load16Le(Input + (uint32_t)positionAfterx1);
        y_refinement = (uint16_t)(uint32_t)r;
        /* start: checking constraint */
        y_refinementConstraintIsOk = (uint32_t)y_refinement >= (uint32_t)x;
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
  uint64_t positionAfterbound;
  uint8_t bound;
  BOOLEAN hasBytes;
  uint64_t positionAftertpointer;
  uint64_t positionAfterS0;
  uint64_t tpointer;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN ok1;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint64_t result;
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
  bound = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = 8ULL <= (InputLength - positionAfterbound);
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
  if (EverParseIsError(positionAftertpointer))
  {
    positionAfterS0 = positionAftertpointer;
  }
  else
  {
    tpointer = Load64Le(Input + (uint32_t)positionAfterbound);
    src64 = tpointer;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    ok = ProbeInit2("_S.tpointer", (uint64_t)4U, Dest);
    if (ok)
    {
      rd = readOffset;
      wr0 = writeOffset;
      ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr0, src64, Dest);
      if (ok1)
      {
        readOffset = rd + (uint64_t)4U;
        writeOffset = wr0 + (uint64_t)4U;
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
    wr = writeOffset;
    hasFailed = failed;
    if (hasFailed)
    {
      ErrorHandlerFn("_S", "tpointer", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    if (b != 0ULL)
    {
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
  uint64_t res;
  uint64_t positionAftertag;
  BOOLEAN hasBytes;
  uint64_t positionAfterspointer;
  uint64_t positionAfterU0;
  uint64_t spointer;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN ok1;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint64_t result;
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
  positionAftertag = res;
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = 8ULL <= (InputLength - positionAftertag);
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
  if (EverParseIsError(positionAfterspointer))
  {
    positionAfterU0 = positionAfterspointer;
  }
  else
  {
    spointer = Load64Le(Input + (uint32_t)positionAftertag);
    src64 = spointer;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    ok = ProbeInit2("_U.spointer", (uint64_t)9U, DestS);
    if (ok)
    {
      rd = readOffset;
      wr0 = writeOffset;
      ok1 = ProbeAndCopy2((uint64_t)9U, rd, wr0, src64, DestS);
      if (ok1)
      {
        readOffset = rd + (uint64_t)9U;
        writeOffset = wr0 + (uint64_t)9U;
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
    wr = writeOffset;
    hasFailed = failed;
    if (hasFailed)
    {
      ErrorHandlerFn("_U", "spointer", "probe", 0ULL, Ctxt, EverParseStreamOf(DestS), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    if (b != 0ULL)
    {
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
  uint64_t positionAftertag;
  uint8_t tag;
  BOOLEAN hasBytes1;
  uint64_t positionAftersptr0;
  uint64_t positionAfterV0;
  uint64_t sptr;
  uint64_t src640;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed0;
  BOOLEAN ok0;
  uint64_t rd0;
  uint64_t wr0;
  BOOLEAN ok10;
  uint64_t wr1;
  BOOLEAN hasFailed;
  uint64_t b0;
  BOOLEAN actionResult;
  uint64_t result0;
  uint64_t positionAftersptr;
  BOOLEAN hasBytes2;
  uint64_t positionAftertptr0;
  uint64_t positionAfterV1;
  uint64_t tptr;
  uint64_t src641;
  uint64_t readOffset0;
  uint64_t writeOffset0;
  BOOLEAN failed1;
  BOOLEAN ok2;
  uint64_t rd1;
  uint64_t wr2;
  BOOLEAN ok11;
  uint64_t wr3;
  BOOLEAN hasFailed0;
  uint64_t b1;
  BOOLEAN actionResult0;
  uint64_t result1;
  uint64_t positionAftertptr;
  BOOLEAN hasBytes;
  uint64_t positionAftert2ptr;
  uint64_t positionAfterV2;
  uint64_t t2ptr;
  uint64_t src64;
  uint64_t readOffset1;
  uint64_t writeOffset1;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t rd;
  uint64_t wr4;
  BOOLEAN ok1;
  uint64_t wr;
  BOOLEAN hasFailed1;
  uint64_t b;
  BOOLEAN actionResult1;
  uint64_t result;
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
  tag = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes1 = 8ULL <= (InputLength - positionAftertag);
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
  if (EverParseIsError(positionAftersptr0))
  {
    positionAfterV0 = positionAftersptr0;
  }
  else
  {
    sptr = Load64Le(Input + (uint32_t)positionAftertag);
    src640 = sptr;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed0 = FALSE;
    ok0 = ProbeInit2("_V.sptr", (uint64_t)9U, DestS);
    if (ok0)
    {
      rd0 = readOffset;
      wr0 = writeOffset;
      ok10 = ProbeAndCopy2((uint64_t)9U, rd0, wr0, src640, DestS);
      if (ok10)
      {
        readOffset = rd0 + (uint64_t)9U;
        writeOffset = wr0 + (uint64_t)9U;
      }
      else
      {
        failed0 = TRUE;
      }
    }
    else
    {
      failed0 = TRUE;
    }
    wr1 = writeOffset;
    hasFailed = failed0;
    if (hasFailed)
    {
      ErrorHandlerFn("_V", "sptr", "probe", 0ULL, Ctxt, EverParseStreamOf(DestS), 0ULL);
      b0 = 0ULL;
    }
    else
    {
      b0 = wr1;
    }
    if (b0 != 0ULL)
    {
      result0 =
        ProbeValidateS(DestT,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestS),
          EverParseStreamLen(DestS),
          0ULL);
      actionResult = !EverParseIsError(result0);
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
  hasBytes2 = 8ULL <= (InputLength - positionAftersptr);
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
  if (EverParseIsError(positionAftertptr0))
  {
    positionAfterV1 = positionAftertptr0;
  }
  else
  {
    tptr = Load64Le(Input + (uint32_t)positionAftersptr);
    src641 = tptr;
    readOffset0 = 0ULL;
    writeOffset0 = 0ULL;
    failed1 = FALSE;
    ok2 = ProbeInit2("_V.tptr", (uint64_t)8U, DestT);
    if (ok2)
    {
      rd1 = readOffset0;
      wr2 = writeOffset0;
      ok11 = ProbeAndCopy2((uint64_t)8U, rd1, wr2, src641, DestT);
      if (ok11)
      {
        readOffset0 = rd1 + (uint64_t)8U;
        writeOffset0 = wr2 + (uint64_t)8U;
      }
      else
      {
        failed1 = TRUE;
      }
    }
    else
    {
      failed1 = TRUE;
    }
    wr3 = writeOffset0;
    hasFailed0 = failed1;
    if (hasFailed0)
    {
      ErrorHandlerFn("_V", "tptr", "probe", 0ULL, Ctxt, EverParseStreamOf(DestT), 0ULL);
      b1 = 0ULL;
    }
    else
    {
      b1 = wr3;
    }
    if (b1 != 0ULL)
    {
      result1 =
        ValidateT((uint32_t)17U,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestT),
          EverParseStreamLen(DestT),
          0ULL);
      actionResult0 = !EverParseIsError(result1);
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
      actionResult0 = FALSE;
    }
    if (actionResult0)
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
  hasBytes = 8ULL <= (InputLength - positionAftertptr);
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
  if (EverParseIsError(positionAftert2ptr))
  {
    positionAfterV2 = positionAftert2ptr;
  }
  else
  {
    t2ptr = Load64Le(Input + (uint32_t)positionAftertptr);
    src64 = t2ptr;
    readOffset1 = 0ULL;
    writeOffset1 = 0ULL;
    failed = FALSE;
    ok = ProbeInit2("_V.t2ptr", (uint64_t)8U, DestT);
    if (ok)
    {
      rd = readOffset1;
      wr4 = writeOffset1;
      ok1 = ProbeAndCopy2((uint64_t)8U, rd, wr4, src64, DestT);
      if (ok1)
      {
        readOffset1 = rd + (uint64_t)8U;
        writeOffset1 = wr4 + (uint64_t)8U;
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
    wr = writeOffset1;
    hasFailed1 = failed;
    if (hasFailed1)
    {
      ErrorHandlerFn("_V", "t2ptr", "probe", 0ULL, Ctxt, EverParseStreamOf(DestT), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    if (b != 0ULL)
    {
      result =
        ValidateT((uint32_t)tag,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestT),
          EverParseStreamLen(DestT),
          0ULL);
      actionResult1 = !EverParseIsError(result);
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
      actionResult1 = FALSE;
    }
    if (actionResult1)
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
  BOOLEAN hasBytes;
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  hasBytes = 9ULL <= (InputLength - StartPosition);
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
  uint64_t positionAfterI;
  uint64_t ttptr;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN ok1;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint8_t *unused;
  uint64_t result;
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
  if (EverParseIsError(positionAfterttptr))
  {
    positionAfterI = positionAfterttptr;
  }
  else
  {
    ttptr = Load64Le(Input + (uint32_t)StartPosition);
    src64 = ttptr;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    ok = ProbeInit2("_I.ttptr", (uint64_t)9U, Dest);
    if (ok)
    {
      rd = readOffset;
      wr0 = writeOffset;
      ok1 = ProbeAndCopy2((uint64_t)9U, rd, wr0, src64, Dest);
      if (ok1)
      {
        readOffset = rd + (uint64_t)9U;
        writeOffset = wr0 + (uint64_t)9U;
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
    wr = writeOffset;
    hasFailed = failed;
    if (hasFailed)
    {
      ErrorHandlerFn("_I", "ttptr", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    if (b != 0ULL)
    {
      unused = EverParseStreamOf(Dest);
      KRML_MAYBE_UNUSED_VAR(unused);
      result = ValidateTt(EverParseStreamLen(Dest), 0ULL);
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
  uint64_t res0;
  uint64_t positionAfterfst;
  BOOLEAN hasBytes1;
  uint64_t positionAfterMultiProbe0;
  uint64_t res1;
  uint64_t positionAftersnd;
  BOOLEAN hasBytes2;
  uint64_t positionAfterMultiProbe1;
  uint64_t res;
  uint64_t positionAftertag;
  BOOLEAN hasBytes3;
  uint64_t positionAftertptr10;
  uint64_t positionAfterMultiProbe2;
  uint64_t tptr1;
  uint64_t src640;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed0;
  BOOLEAN ok0;
  uint64_t rd0;
  uint64_t wr0;
  BOOLEAN ok10;
  uint64_t wr1;
  BOOLEAN hasFailed;
  uint64_t b0;
  BOOLEAN actionResult;
  uint64_t result0;
  uint64_t positionAftertptr1;
  BOOLEAN hasBytes;
  uint64_t positionAftertptr2;
  uint64_t positionAfterMultiProbe3;
  uint64_t tptr2;
  uint64_t src64;
  uint64_t readOffset0;
  uint64_t writeOffset0;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t rd;
  uint64_t wr2;
  BOOLEAN ok1;
  uint64_t wr;
  BOOLEAN hasFailed0;
  uint64_t b;
  BOOLEAN actionResult0;
  uint64_t result;
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
  positionAfterfst = res0;
  if (EverParseIsError(positionAfterfst))
  {
    return positionAfterfst;
  }
  /* Validating field snd */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes1 = 4ULL <= (InputLength - positionAfterfst);
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
  positionAftersnd = res1;
  if (EverParseIsError(positionAftersnd))
  {
    return positionAftersnd;
  }
  /* Validating field tag */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  hasBytes2 = 1ULL <= (InputLength - positionAftersnd);
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
  positionAftertag = res;
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes3 = 8ULL <= (InputLength - positionAftertag);
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
  if (EverParseIsError(positionAftertptr10))
  {
    positionAfterMultiProbe2 = positionAftertptr10;
  }
  else
  {
    tptr1 = Load64Le(Input + (uint32_t)positionAftertag);
    src640 = tptr1;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed0 = FALSE;
    ok0 = ProbeInit2("_MultiProbe.tptr1", (uint64_t)4U, DestT1);
    if (ok0)
    {
      rd0 = readOffset;
      wr0 = writeOffset;
      ok10 = ProbeAndCopy2((uint64_t)4U, rd0, wr0, src640, DestT1);
      if (ok10)
      {
        readOffset = rd0 + (uint64_t)4U;
        writeOffset = wr0 + (uint64_t)4U;
      }
      else
      {
        failed0 = TRUE;
      }
    }
    else
    {
      failed0 = TRUE;
    }
    wr1 = writeOffset;
    hasFailed = failed0;
    if (hasFailed)
    {
      ErrorHandlerFn("_MultiProbe", "tptr1", "probe", 0ULL, Ctxt, EverParseStreamOf(DestT1), 0ULL);
      b0 = 0ULL;
    }
    else
    {
      b0 = wr1;
    }
    if (b0 != 0ULL)
    {
      result0 =
        ValidateT((uint32_t)17U,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestT1),
          EverParseStreamLen(DestT1),
          0ULL);
      actionResult = !EverParseIsError(result0);
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
  hasBytes = 8ULL <= (InputLength - positionAftertptr1);
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
  if (EverParseIsError(positionAftertptr2))
  {
    positionAfterMultiProbe3 = positionAftertptr2;
  }
  else
  {
    tptr2 = Load64Le(Input + (uint32_t)positionAftertptr1);
    src64 = tptr2;
    readOffset0 = 0ULL;
    writeOffset0 = 0ULL;
    failed = FALSE;
    ok = ProbeInit2("_MultiProbe.tptr2", (uint64_t)4U, DestT2);
    if (ok)
    {
      rd = readOffset0;
      wr2 = writeOffset0;
      ok1 = ProbeAndCopyAlt((uint64_t)4U, rd, wr2, src64, DestT2);
      if (ok1)
      {
        readOffset0 = rd + (uint64_t)4U;
        writeOffset0 = wr2 + (uint64_t)4U;
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
    wr = writeOffset0;
    hasFailed0 = failed;
    if (hasFailed0)
    {
      ErrorHandlerFn("_MultiProbe", "tptr2", "probe", 0ULL, Ctxt, EverParseStreamOf(DestT2), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    if (b != 0ULL)
    {
      result =
        ValidateT((uint32_t)42U,
          Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(DestT2),
          EverParseStreamLen(DestT2),
          0ULL);
      actionResult0 = !EverParseIsError(result);
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
      actionResult0 = FALSE;
    }
    if (actionResult0)
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
  uint64_t positionAfterBound;
  uint32_t bound;
  BOOLEAN hasBytes;
  uint64_t positionAfterptr;
  uint64_t positionAfterMaybeT0;
  uint64_t ptr;
  uint64_t src64;
  BOOLEAN actionResult;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN ok1;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  uint64_t result;
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
  bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = 8ULL <= (InputLength - positionAfterBound);
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
  if (EverParseIsError(positionAfterptr))
  {
    positionAfterMaybeT0 = positionAfterptr;
  }
  else
  {
    ptr = Load64Le(Input + (uint32_t)positionAfterBound);
    src64 = ptr;
    if (src64 == 0ULL)
    {
      actionResult = TRUE;
    }
    else
    {
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit2("_MaybeT.ptr", (uint64_t)4U, Dest);
      if (ok)
      {
        rd = readOffset;
        wr0 = writeOffset;
        ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr0, src64, Dest);
        if (ok1)
        {
          readOffset = rd + (uint64_t)4U;
          writeOffset = wr0 + (uint64_t)4U;
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
      wr = writeOffset;
      hasFailed = failed;
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
  uint64_t positionAfterBound;
  uint32_t bound;
  BOOLEAN hasBytes;
  uint64_t positionAfterptr;
  uint64_t positionAfterCoercePtr0;
  uint32_t ptr;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN ok;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN ok1;
  uint64_t wr;
  BOOLEAN hasFailed;
  uint64_t b;
  BOOLEAN actionResult;
  uint64_t result;
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
  bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = 4ULL <= (InputLength - positionAfterBound);
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
  if (EverParseIsError(positionAfterptr))
  {
    positionAfterCoercePtr0 = positionAfterptr;
  }
  else
  {
    ptr = Load32Le(Input + (uint32_t)positionAfterBound);
    src64 = UlongToPtr2(ptr);
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    ok = ProbeInit2("_CoercePtr.ptr", (uint64_t)4U, Dest);
    if (ok)
    {
      rd = readOffset;
      wr0 = writeOffset;
      ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr0, src64, Dest);
      if (ok1)
      {
        readOffset = rd + (uint64_t)4U;
        writeOffset = wr0 + (uint64_t)4U;
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
    wr = writeOffset;
    hasFailed = failed;
    if (hasFailed)
    {
      ErrorHandlerFn("_CoercePtr", "ptr", "probe", 0ULL, Ctxt, EverParseStreamOf(Dest), 0ULL);
      b = 0ULL;
    }
    else
    {
      b = wr;
    }
    if (b != 0ULL)
    {
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

uint64_t
ProbeValidateProbeOnly(
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
  BOOLEAN hasBytes;
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  hasBytes = 8ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 8ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

uint64_t
ProbeValidateBothEntrypoints(
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
  BOOLEAN hasBytes;
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  hasBytes = 8ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 8ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

uint64_t
ProbeValidateNamedPlainEp(
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
  BOOLEAN hasBytes;
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  hasBytes = 8ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 8ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

uint64_t
ProbeValidateNamedProbeEp(
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
  BOOLEAN hasBytes;
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  hasBytes = 8ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 8ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

uint64_t
ProbeValidateNamedBothEp(
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
  BOOLEAN hasBytes;
  KRML_MAYBE_UNUSED_VAR(Ctxt);
  KRML_MAYBE_UNUSED_VAR(ErrorHandlerFn);
  KRML_MAYBE_UNUSED_VAR(Input);
  hasBytes = 8ULL <= (InputLength - StartPosition);
  if (hasBytes)
  {
    return StartPosition + 8ULL;
  }
  return EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
}

