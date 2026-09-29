

#include "Probe.h"

#include "Probe_ExternalAPI.h"
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
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 2ULL;
  uint64_t positionAfterx0;
  uint64_t positionAfterx;
  uint16_t x;
  BOOLEAN xConstraintIsOk;
  uint64_t positionAfterCheckedx;
  BOOLEAN hasBytes;
  uint64_t positionAftery_refinement;
  uint64_t positionAftery_refinement0;
  uint16_t y_refinement;
  BOOLEAN y_refinementConstraintIsOk;
  if (hasBytes0)
  {
    positionAfterx0 = StartPosition + 2ULL;
  }
  else
  {
    positionAfterx0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterx0))
  {
    positionAfterx = positionAfterx0;
  }
  else
  {
    x = Load16Le(Input + (uint32_t)StartPosition);
    xConstraintIsOk = (uint32_t)x >= Bound;
    positionAfterCheckedx = EverParseCheckConstraintOk(xConstraintIsOk, positionAfterx0);
    if (EverParseIsError(positionAfterCheckedx))
    {
      positionAfterx = positionAfterCheckedx;
    }
    else
    {
      /* Validating field y */
      /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
      hasBytes = (InputLength - positionAfterCheckedx) >= 2ULL;
      if (hasBytes)
      {
        positionAftery_refinement = positionAfterCheckedx + 2ULL;
      }
      else
      {
        positionAftery_refinement =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedx);
      }
      if (EverParseIsError(positionAftery_refinement))
      {
        positionAftery_refinement0 = positionAftery_refinement;
      }
      else
      {
        /* reading field_value */
        y_refinement = Load16Le(Input + (uint32_t)positionAfterCheckedx);
        /* start: checking constraint */
        y_refinementConstraintIsOk = y_refinement >= x;
        /* end: checking constraint */
        positionAftery_refinement0 =
          EverParseCheckConstraintOk(y_refinementConstraintIsOk,
            positionAftery_refinement);
      }
      if (EverParseIsSuccess(positionAftery_refinement0))
      {
        positionAfterx = positionAftery_refinement0;
      }
      else
      {
        ErrorHandlerFn("_T",
          "y.refinement",
          EverParseErrorReasonOfResult(positionAftery_refinement0),
          EverParseGetValidatorErrorKind(positionAftery_refinement0),
          Ctxt,
          Input,
          positionAfterCheckedx);
        positionAfterx = positionAftery_refinement0;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterx))
  {
    return positionAfterx;
  }
  ErrorHandlerFn("_T",
    "x",
    EverParseErrorReasonOfResult(positionAfterx),
    EverParseGetValidatorErrorKind(positionAfterx),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterx;
}

uint64_t
ProbeValidateS(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 1ULL;
  uint64_t positionAfterbound0;
  uint64_t positionAfterbound;
  uint8_t bound;
  BOOLEAN hasBytes;
  uint64_t positionAftertpointer0;
  uint64_t positionAftertpointer;
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
    positionAfterbound0 = StartPosition + 1ULL;
  }
  else
  {
    positionAfterbound0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterbound0))
  {
    positionAfterbound = positionAfterbound0;
  }
  else
  {
    ErrorHandlerFn("_S",
      "bound",
      EverParseErrorReasonOfResult(positionAfterbound0),
      EverParseGetValidatorErrorKind(positionAfterbound0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterbound = positionAfterbound0;
  }
  if (EverParseIsError(positionAfterbound))
  {
    return positionAfterbound;
  }
  bound = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = (InputLength - positionAfterbound) >= 8ULL;
  if (hasBytes)
  {
    positionAftertpointer0 = positionAfterbound + 8ULL;
  }
  else
  {
    positionAftertpointer0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterbound);
  }
  if (EverParseIsError(positionAftertpointer0))
  {
    positionAftertpointer = positionAftertpointer0;
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
      positionAftertpointer = positionAftertpointer0;
    }
    else
    {
      positionAftertpointer =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftertpointer0);
    }
  }
  if (EverParseIsSuccess(positionAftertpointer))
  {
    return positionAftertpointer;
  }
  ErrorHandlerFn("_S",
    "tpointer",
    EverParseErrorReasonOfResult(positionAftertpointer),
    EverParseGetValidatorErrorKind(positionAftertpointer),
    Ctxt,
    Input,
    positionAfterbound);
  return positionAftertpointer;
}

uint64_t
ProbeValidateU(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field tag */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 1ULL;
  uint64_t positionAftertag0;
  uint64_t res;
  uint64_t positionAftertag;
  BOOLEAN hasBytes;
  uint64_t positionAfterspointer0;
  uint64_t positionAfterspointer;
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
    positionAftertag0 = StartPosition + 1ULL;
  }
  else
  {
    positionAftertag0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAftertag0))
  {
    res = positionAftertag0;
  }
  else
  {
    ErrorHandlerFn("_U",
      "tag",
      EverParseErrorReasonOfResult(positionAftertag0),
      EverParseGetValidatorErrorKind(positionAftertag0),
      Ctxt,
      Input,
      StartPosition);
    res = positionAftertag0;
  }
  positionAftertag = res;
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = (InputLength - positionAftertag) >= 8ULL;
  if (hasBytes)
  {
    positionAfterspointer0 = positionAftertag + 8ULL;
  }
  else
  {
    positionAfterspointer0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertag);
  }
  if (EverParseIsError(positionAfterspointer0))
  {
    positionAfterspointer = positionAfterspointer0;
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
      positionAfterspointer = positionAfterspointer0;
    }
    else
    {
      positionAfterspointer =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterspointer0);
    }
  }
  if (EverParseIsSuccess(positionAfterspointer))
  {
    return positionAfterspointer;
  }
  ErrorHandlerFn("_U",
    "spointer",
    EverParseErrorReasonOfResult(positionAfterspointer),
    EverParseGetValidatorErrorKind(positionAfterspointer),
    Ctxt,
    Input,
    positionAftertag);
  return positionAfterspointer;
}

uint64_t
ProbeValidateV(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 1ULL;
  uint64_t positionAftertag0;
  uint64_t positionAftertag;
  uint8_t tag;
  BOOLEAN hasBytes1;
  uint64_t positionAftersptr0;
  uint64_t positionAftersptr1;
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
  uint64_t positionAftertptr1;
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
  uint64_t positionAftert2ptr0;
  uint64_t positionAftert2ptr;
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
    positionAftertag0 = StartPosition + 1ULL;
  }
  else
  {
    positionAftertag0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAftertag0))
  {
    positionAftertag = positionAftertag0;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tag",
      EverParseErrorReasonOfResult(positionAftertag0),
      EverParseGetValidatorErrorKind(positionAftertag0),
      Ctxt,
      Input,
      StartPosition);
    positionAftertag = positionAftertag0;
  }
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  tag = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes1 = (InputLength - positionAftertag) >= 8ULL;
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
    positionAftersptr1 = positionAftersptr0;
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
      positionAftersptr1 = positionAftersptr0;
    }
    else
    {
      positionAftersptr1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftersptr0);
    }
  }
  if (EverParseIsSuccess(positionAftersptr1))
  {
    positionAftersptr = positionAftersptr1;
  }
  else
  {
    ErrorHandlerFn("_V",
      "sptr",
      EverParseErrorReasonOfResult(positionAftersptr1),
      EverParseGetValidatorErrorKind(positionAftersptr1),
      Ctxt,
      Input,
      positionAftertag);
    positionAftersptr = positionAftersptr1;
  }
  if (EverParseIsError(positionAftersptr))
  {
    return positionAftersptr;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes2 = (InputLength - positionAftersptr) >= 8ULL;
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
    positionAftertptr1 = positionAftertptr0;
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
      positionAftertptr1 = positionAftertptr0;
    }
    else
    {
      positionAftertptr1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftertptr0);
    }
  }
  if (EverParseIsSuccess(positionAftertptr1))
  {
    positionAftertptr = positionAftertptr1;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tptr",
      EverParseErrorReasonOfResult(positionAftertptr1),
      EverParseGetValidatorErrorKind(positionAftertptr1),
      Ctxt,
      Input,
      positionAftersptr);
    positionAftertptr = positionAftertptr1;
  }
  if (EverParseIsError(positionAftertptr))
  {
    return positionAftertptr;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = (InputLength - positionAftertptr) >= 8ULL;
  if (hasBytes)
  {
    positionAftert2ptr0 = positionAftertptr + 8ULL;
  }
  else
  {
    positionAftert2ptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertptr);
  }
  if (EverParseIsError(positionAftert2ptr0))
  {
    positionAftert2ptr = positionAftert2ptr0;
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
      positionAftert2ptr = positionAftert2ptr0;
    }
    else
    {
      positionAftert2ptr =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftert2ptr0);
    }
  }
  if (EverParseIsSuccess(positionAftert2ptr))
  {
    return positionAftert2ptr;
  }
  ErrorHandlerFn("_V",
    "t2ptr",
    EverParseErrorReasonOfResult(positionAftert2ptr),
    EverParseGetValidatorErrorKind(positionAftert2ptr),
    Ctxt,
    Input,
    positionAftertptr);
  return positionAftert2ptr;
}

uint64_t
ProbeValidateIndirect(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 9ULL;
  uint64_t res;
  uint64_t positionAfterfst;
  if (hasBytes)
  {
    res = StartPosition + 9ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterfst = res;
  if (EverParseIsSuccess(positionAfterfst))
  {
    return positionAfterfst;
  }
  ErrorHandlerFn("_Indirect",
    "fst",
    EverParseErrorReasonOfResult(positionAfterfst),
    EverParseGetValidatorErrorKind(positionAfterfst),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterfst;
}

static inline uint64_t
ValidateTt(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 9ULL;
  uint64_t res;
  uint64_t positionAfterfst;
  if (hasBytes)
  {
    res = StartPosition + 9ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterfst = res;
  if (EverParseIsSuccess(positionAfterfst))
  {
    return positionAfterfst;
  }
  ErrorHandlerFn("_TT",
    "fst",
    EverParseErrorReasonOfResult(positionAfterfst),
    EverParseGetValidatorErrorKind(positionAfterfst),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterfst;
}

uint64_t
ProbeValidateI(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 8ULL;
  uint64_t positionAfterttptr0;
  uint64_t positionAfterttptr;
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
  uint64_t result;
  if (hasBytes)
  {
    positionAfterttptr0 = StartPosition + 8ULL;
  }
  else
  {
    positionAfterttptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterttptr0))
  {
    positionAfterttptr = positionAfterttptr0;
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
      result =
        ValidateTt(Ctxt,
          ErrorHandlerFn,
          EverParseStreamOf(Dest),
          EverParseStreamLen(Dest),
          0ULL);
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
      positionAfterttptr = positionAfterttptr0;
    }
    else
    {
      positionAfterttptr =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterttptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterttptr))
  {
    return positionAfterttptr;
  }
  ErrorHandlerFn("_I",
    "ttptr",
    EverParseErrorReasonOfResult(positionAfterttptr),
    EverParseGetValidatorErrorKind(positionAfterttptr),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterttptr;
}

uint64_t
ProbeValidateMultiProbe(
  EVERPARSE_COPY_BUFFER_T DestT1,
  EVERPARSE_COPY_BUFFER_T DestT2,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field fst */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterfst0;
  uint64_t res0;
  uint64_t positionAfterfst;
  BOOLEAN hasBytes1;
  uint64_t positionAftersnd0;
  uint64_t res1;
  uint64_t positionAftersnd;
  BOOLEAN hasBytes2;
  uint64_t positionAftertag0;
  uint64_t res;
  uint64_t positionAftertag;
  BOOLEAN hasBytes3;
  uint64_t positionAftertptr10;
  uint64_t positionAftertptr11;
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
  uint64_t positionAftertptr20;
  uint64_t positionAftertptr2;
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
    positionAfterfst0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterfst0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterfst0))
  {
    res0 = positionAfterfst0;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "fst",
      EverParseErrorReasonOfResult(positionAfterfst0),
      EverParseGetValidatorErrorKind(positionAfterfst0),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterfst0;
  }
  positionAfterfst = res0;
  if (EverParseIsError(positionAfterfst))
  {
    return positionAfterfst;
  }
  /* Validating field snd */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes1 = (InputLength - positionAfterfst) >= 4ULL;
  if (hasBytes1)
  {
    positionAftersnd0 = positionAfterfst + 4ULL;
  }
  else
  {
    positionAftersnd0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterfst);
  }
  if (EverParseIsSuccess(positionAftersnd0))
  {
    res1 = positionAftersnd0;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "snd",
      EverParseErrorReasonOfResult(positionAftersnd0),
      EverParseGetValidatorErrorKind(positionAftersnd0),
      Ctxt,
      Input,
      positionAfterfst);
    res1 = positionAftersnd0;
  }
  positionAftersnd = res1;
  if (EverParseIsError(positionAftersnd))
  {
    return positionAftersnd;
  }
  /* Validating field tag */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  hasBytes2 = (InputLength - positionAftersnd) >= 1ULL;
  if (hasBytes2)
  {
    positionAftertag0 = positionAftersnd + 1ULL;
  }
  else
  {
    positionAftertag0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftersnd);
  }
  if (EverParseIsSuccess(positionAftertag0))
  {
    res = positionAftertag0;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "tag",
      EverParseErrorReasonOfResult(positionAftertag0),
      EverParseGetValidatorErrorKind(positionAftertag0),
      Ctxt,
      Input,
      positionAftersnd);
    res = positionAftertag0;
  }
  positionAftertag = res;
  if (EverParseIsError(positionAftertag))
  {
    return positionAftertag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes3 = (InputLength - positionAftertag) >= 8ULL;
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
    positionAftertptr11 = positionAftertptr10;
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
      positionAftertptr11 = positionAftertptr10;
    }
    else
    {
      positionAftertptr11 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftertptr10);
    }
  }
  if (EverParseIsSuccess(positionAftertptr11))
  {
    positionAftertptr1 = positionAftertptr11;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "tptr1",
      EverParseErrorReasonOfResult(positionAftertptr11),
      EverParseGetValidatorErrorKind(positionAftertptr11),
      Ctxt,
      Input,
      positionAftertag);
    positionAftertptr1 = positionAftertptr11;
  }
  if (EverParseIsError(positionAftertptr1))
  {
    return positionAftertptr1;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = (InputLength - positionAftertptr1) >= 8ULL;
  if (hasBytes)
  {
    positionAftertptr20 = positionAftertptr1 + 8ULL;
  }
  else
  {
    positionAftertptr20 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAftertptr1);
  }
  if (EverParseIsError(positionAftertptr20))
  {
    positionAftertptr2 = positionAftertptr20;
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
      positionAftertptr2 = positionAftertptr20;
    }
    else
    {
      positionAftertptr2 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAftertptr20);
    }
  }
  if (EverParseIsSuccess(positionAftertptr2))
  {
    return positionAftertptr2;
  }
  ErrorHandlerFn("_MultiProbe",
    "tptr2",
    EverParseErrorReasonOfResult(positionAftertptr2),
    EverParseGetValidatorErrorKind(positionAftertptr2),
    Ctxt,
    Input,
    positionAftertptr1);
  return positionAftertptr2;
}

uint64_t
ProbeValidateMaybeT(
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
  uint64_t positionAfterBound0;
  uint64_t positionAfterBound;
  uint32_t bound;
  BOOLEAN hasBytes;
  uint64_t positionAfterptr0;
  uint64_t positionAfterptr;
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
    positionAfterBound0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterBound0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBound0))
  {
    positionAfterBound = positionAfterBound0;
  }
  else
  {
    ErrorHandlerFn("_MaybeT",
      "Bound",
      EverParseErrorReasonOfResult(positionAfterBound0),
      EverParseGetValidatorErrorKind(positionAfterBound0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBound = positionAfterBound0;
  }
  if (EverParseIsError(positionAfterBound))
  {
    return positionAfterBound;
  }
  bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytes = (InputLength - positionAfterBound) >= 8ULL;
  if (hasBytes)
  {
    positionAfterptr0 = positionAfterBound + 8ULL;
  }
  else
  {
    positionAfterptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  if (EverParseIsError(positionAfterptr0))
  {
    positionAfterptr = positionAfterptr0;
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
      positionAfterptr = positionAfterptr0;
    }
    else
    {
      positionAfterptr =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterptr))
  {
    return positionAfterptr;
  }
  ErrorHandlerFn("_MaybeT",
    "ptr",
    EverParseErrorReasonOfResult(positionAfterptr),
    EverParseGetValidatorErrorKind(positionAfterptr),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterptr;
}

uint64_t
ProbeValidateCoercePtr(
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
  uint64_t positionAfterBound0;
  uint64_t positionAfterBound;
  uint32_t bound;
  BOOLEAN hasBytes;
  uint64_t positionAfterptr0;
  uint64_t positionAfterptr;
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
    positionAfterBound0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterBound0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBound0))
  {
    positionAfterBound = positionAfterBound0;
  }
  else
  {
    ErrorHandlerFn("_CoercePtr",
      "Bound",
      EverParseErrorReasonOfResult(positionAfterBound0),
      EverParseGetValidatorErrorKind(positionAfterBound0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBound = positionAfterBound0;
  }
  if (EverParseIsError(positionAfterBound))
  {
    return positionAfterBound;
  }
  bound = Load32Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytes = (InputLength - positionAfterBound) >= 4ULL;
  if (hasBytes)
  {
    positionAfterptr0 = positionAfterBound + 4ULL;
  }
  else
  {
    positionAfterptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  if (EverParseIsError(positionAfterptr0))
  {
    positionAfterptr = positionAfterptr0;
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
      positionAfterptr = positionAfterptr0;
    }
    else
    {
      positionAfterptr =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterptr))
  {
    return positionAfterptr;
  }
  ErrorHandlerFn("_CoercePtr",
    "ptr",
    EverParseErrorReasonOfResult(positionAfterptr),
    EverParseGetValidatorErrorKind(positionAfterptr),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterptr;
}

uint64_t
ProbeValidateProbeOnly(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterx;
  if (hasBytes)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterx = res;
  if (EverParseIsSuccess(positionAfterx))
  {
    return positionAfterx;
  }
  ErrorHandlerFn("_ProbeOnly",
    "x",
    EverParseErrorReasonOfResult(positionAfterx),
    EverParseGetValidatorErrorKind(positionAfterx),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterx;
}

uint64_t
ProbeValidateBothEntrypoints(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterx;
  if (hasBytes)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterx = res;
  if (EverParseIsSuccess(positionAfterx))
  {
    return positionAfterx;
  }
  ErrorHandlerFn("_BothEntrypoints",
    "x",
    EverParseErrorReasonOfResult(positionAfterx),
    EverParseGetValidatorErrorKind(positionAfterx),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterx;
}

uint64_t
ProbeValidateNamedPlainEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterx;
  if (hasBytes)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterx = res;
  if (EverParseIsSuccess(positionAfterx))
  {
    return positionAfterx;
  }
  ErrorHandlerFn("_NamedPlainEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterx),
    EverParseGetValidatorErrorKind(positionAfterx),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterx;
}

uint64_t
ProbeValidateNamedProbeEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterx;
  if (hasBytes)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterx = res;
  if (EverParseIsSuccess(positionAfterx))
  {
    return positionAfterx;
  }
  ErrorHandlerFn("_NamedProbeEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterx),
    EverParseGetValidatorErrorKind(positionAfterx),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterx;
}

uint64_t
ProbeValidateNamedBothEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterx;
  if (hasBytes)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterx = res;
  if (EverParseIsSuccess(positionAfterx))
  {
    return positionAfterx;
  }
  ErrorHandlerFn("_NamedBothEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterx),
    EverParseGetValidatorErrorKind(positionAfterx),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterx;
}

