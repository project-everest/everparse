

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
  BOOLEAN hasBytesForX = (InputLength - StartPosition) >= 2ULL;
  uint64_t positionAfterX0;
  uint64_t positionAfterX;
  uint16_t x;
  BOOLEAN xConstraintIsOk;
  uint64_t positionAfterCheckedX;
  BOOLEAN hasBytesForY_refinement;
  uint64_t positionAfterY_refinement;
  uint64_t positionAfterY_refinement0;
  uint16_t y_refinement;
  BOOLEAN y_refinementConstraintIsOk;
  if (hasBytesForX)
  {
    positionAfterX0 = StartPosition + 2ULL;
  }
  else
  {
    positionAfterX0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterX0))
  {
    positionAfterX = positionAfterX0;
  }
  else
  {
    x = Load16Le(Input + (uint32_t)StartPosition);
    xConstraintIsOk = (uint32_t)x >= Bound;
    positionAfterCheckedX = EverParseCheckConstraintOk(xConstraintIsOk, positionAfterX0);
    if (EverParseIsError(positionAfterCheckedX))
    {
      positionAfterX = positionAfterCheckedX;
    }
    else
    {
      /* Validating field y */
      /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
      hasBytesForY_refinement = (InputLength - positionAfterCheckedX) >= 2ULL;
      if (hasBytesForY_refinement)
      {
        positionAfterY_refinement = positionAfterCheckedX + 2ULL;
      }
      else
      {
        positionAfterY_refinement =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedX);
      }
      if (EverParseIsError(positionAfterY_refinement))
      {
        positionAfterY_refinement0 = positionAfterY_refinement;
      }
      else
      {
        /* reading field_value */
        y_refinement = Load16Le(Input + (uint32_t)positionAfterCheckedX);
        /* start: checking constraint */
        y_refinementConstraintIsOk = y_refinement >= x;
        /* end: checking constraint */
        positionAfterY_refinement0 =
          EverParseCheckConstraintOk(y_refinementConstraintIsOk,
            positionAfterY_refinement);
      }
      if (EverParseIsSuccess(positionAfterY_refinement0))
      {
        positionAfterX = positionAfterY_refinement0;
      }
      else
      {
        ErrorHandlerFn("_T",
          "y.refinement",
          EverParseErrorReasonOfResult(positionAfterY_refinement0),
          EverParseGetValidatorErrorKind(positionAfterY_refinement0),
          Ctxt,
          Input,
          positionAfterCheckedX);
        positionAfterX = positionAfterY_refinement0;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterX))
  {
    return positionAfterX;
  }
  ErrorHandlerFn("_T",
    "x",
    EverParseErrorReasonOfResult(positionAfterX),
    EverParseGetValidatorErrorKind(positionAfterX),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX;
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
  BOOLEAN hasBytesForBound = (InputLength - StartPosition) >= 1ULL;
  uint64_t positionAfterBound0;
  uint64_t positionAfterBound;
  uint8_t bound;
  BOOLEAN hasBytesForTpointer;
  uint64_t positionAfterTpointer0;
  uint64_t positionAfterTpointer;
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
  if (hasBytesForBound)
  {
    positionAfterBound0 = StartPosition + 1ULL;
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
    ErrorHandlerFn("_S",
      "bound",
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
  bound = Input[(uint32_t)StartPosition];
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForTpointer = (InputLength - positionAfterBound) >= 8ULL;
  if (hasBytesForTpointer)
  {
    positionAfterTpointer0 = positionAfterBound + 8ULL;
  }
  else
  {
    positionAfterTpointer0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  if (EverParseIsError(positionAfterTpointer0))
  {
    positionAfterTpointer = positionAfterTpointer0;
  }
  else
  {
    tpointer = Load64Le(Input + (uint32_t)positionAfterBound);
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
        positionAfterBound);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterTpointer = positionAfterTpointer0;
    }
    else
    {
      positionAfterTpointer =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTpointer0);
    }
  }
  if (EverParseIsSuccess(positionAfterTpointer))
  {
    return positionAfterTpointer;
  }
  ErrorHandlerFn("_S",
    "tpointer",
    EverParseErrorReasonOfResult(positionAfterTpointer),
    EverParseGetValidatorErrorKind(positionAfterTpointer),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterTpointer;
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
  BOOLEAN hasBytesForTag = (InputLength - StartPosition) >= 1ULL;
  uint64_t positionAfterTag0;
  uint64_t res;
  uint64_t positionAfterTag;
  BOOLEAN hasBytesForSpointer;
  uint64_t positionAfterSpointer0;
  uint64_t positionAfterSpointer;
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
  if (hasBytesForTag)
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
    res = positionAfterTag0;
  }
  else
  {
    ErrorHandlerFn("_U",
      "tag",
      EverParseErrorReasonOfResult(positionAfterTag0),
      EverParseGetValidatorErrorKind(positionAfterTag0),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterTag0;
  }
  positionAfterTag = res;
  if (EverParseIsError(positionAfterTag))
  {
    return positionAfterTag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForSpointer = (InputLength - positionAfterTag) >= 8ULL;
  if (hasBytesForSpointer)
  {
    positionAfterSpointer0 = positionAfterTag + 8ULL;
  }
  else
  {
    positionAfterSpointer0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTag);
  }
  if (EverParseIsError(positionAfterSpointer0))
  {
    positionAfterSpointer = positionAfterSpointer0;
  }
  else
  {
    spointer = Load64Le(Input + (uint32_t)positionAfterTag);
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
        positionAfterTag);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterSpointer = positionAfterSpointer0;
    }
    else
    {
      positionAfterSpointer =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterSpointer0);
    }
  }
  if (EverParseIsSuccess(positionAfterSpointer))
  {
    return positionAfterSpointer;
  }
  ErrorHandlerFn("_U",
    "spointer",
    EverParseErrorReasonOfResult(positionAfterSpointer),
    EverParseGetValidatorErrorKind(positionAfterSpointer),
    Ctxt,
    Input,
    positionAfterTag);
  return positionAfterSpointer;
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
  BOOLEAN hasBytesForTag = (InputLength - StartPosition) >= 1ULL;
  uint64_t positionAfterTag0;
  uint64_t positionAfterTag;
  uint8_t tag;
  BOOLEAN hasBytesForSptr;
  uint64_t positionAfterSptr0;
  uint64_t positionAfterSptr1;
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
  uint64_t positionAfterSptr;
  BOOLEAN hasBytesForTptr;
  uint64_t positionAfterTptr0;
  uint64_t positionAfterTptr1;
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
  uint64_t positionAfterTptr;
  BOOLEAN hasBytesForT2ptr;
  uint64_t positionAfterT2ptr0;
  uint64_t positionAfterT2ptr;
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
  if (hasBytesForTag)
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
    ErrorHandlerFn("_V",
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
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForSptr = (InputLength - positionAfterTag) >= 8ULL;
  if (hasBytesForSptr)
  {
    positionAfterSptr0 = positionAfterTag + 8ULL;
  }
  else
  {
    positionAfterSptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTag);
  }
  if (EverParseIsError(positionAfterSptr0))
  {
    positionAfterSptr1 = positionAfterSptr0;
  }
  else
  {
    sptr = Load64Le(Input + (uint32_t)positionAfterTag);
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
        positionAfterTag);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterSptr1 = positionAfterSptr0;
    }
    else
    {
      positionAfterSptr1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterSptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterSptr1))
  {
    positionAfterSptr = positionAfterSptr1;
  }
  else
  {
    ErrorHandlerFn("_V",
      "sptr",
      EverParseErrorReasonOfResult(positionAfterSptr1),
      EverParseGetValidatorErrorKind(positionAfterSptr1),
      Ctxt,
      Input,
      positionAfterTag);
    positionAfterSptr = positionAfterSptr1;
  }
  if (EverParseIsError(positionAfterSptr))
  {
    return positionAfterSptr;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForTptr = (InputLength - positionAfterSptr) >= 8ULL;
  if (hasBytesForTptr)
  {
    positionAfterTptr0 = positionAfterSptr + 8ULL;
  }
  else
  {
    positionAfterTptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterSptr);
  }
  if (EverParseIsError(positionAfterTptr0))
  {
    positionAfterTptr1 = positionAfterTptr0;
  }
  else
  {
    tptr = Load64Le(Input + (uint32_t)positionAfterSptr);
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
        positionAfterSptr);
      actionResult0 = FALSE;
    }
    if (actionResult0)
    {
      positionAfterTptr1 = positionAfterTptr0;
    }
    else
    {
      positionAfterTptr1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterTptr1))
  {
    positionAfterTptr = positionAfterTptr1;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tptr",
      EverParseErrorReasonOfResult(positionAfterTptr1),
      EverParseGetValidatorErrorKind(positionAfterTptr1),
      Ctxt,
      Input,
      positionAfterSptr);
    positionAfterTptr = positionAfterTptr1;
  }
  if (EverParseIsError(positionAfterTptr))
  {
    return positionAfterTptr;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForT2ptr = (InputLength - positionAfterTptr) >= 8ULL;
  if (hasBytesForT2ptr)
  {
    positionAfterT2ptr0 = positionAfterTptr + 8ULL;
  }
  else
  {
    positionAfterT2ptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTptr);
  }
  if (EverParseIsError(positionAfterT2ptr0))
  {
    positionAfterT2ptr = positionAfterT2ptr0;
  }
  else
  {
    t2ptr = Load64Le(Input + (uint32_t)positionAfterTptr);
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
        positionAfterTptr);
      actionResult1 = FALSE;
    }
    if (actionResult1)
    {
      positionAfterT2ptr = positionAfterT2ptr0;
    }
    else
    {
      positionAfterT2ptr =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterT2ptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterT2ptr))
  {
    return positionAfterT2ptr;
  }
  ErrorHandlerFn("_V",
    "t2ptr",
    EverParseErrorReasonOfResult(positionAfterT2ptr),
    EverParseGetValidatorErrorKind(positionAfterT2ptr),
    Ctxt,
    Input,
    positionAfterTptr);
  return positionAfterT2ptr;
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
  BOOLEAN hasBytesForFstSndTag = (InputLength - StartPosition) >= 9ULL;
  uint64_t res;
  uint64_t positionAfterFst;
  if (hasBytesForFstSndTag)
  {
    res = StartPosition + 9ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterFst = res;
  if (EverParseIsSuccess(positionAfterFst))
  {
    return positionAfterFst;
  }
  ErrorHandlerFn("_Indirect",
    "fst",
    EverParseErrorReasonOfResult(positionAfterFst),
    EverParseGetValidatorErrorKind(positionAfterFst),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterFst;
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
  BOOLEAN hasBytesForFstSndTag = (InputLength - StartPosition) >= 9ULL;
  uint64_t res;
  uint64_t positionAfterFst;
  if (hasBytesForFstSndTag)
  {
    res = StartPosition + 9ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterFst = res;
  if (EverParseIsSuccess(positionAfterFst))
  {
    return positionAfterFst;
  }
  ErrorHandlerFn("_TT",
    "fst",
    EverParseErrorReasonOfResult(positionAfterFst),
    EverParseGetValidatorErrorKind(positionAfterFst),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterFst;
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
  BOOLEAN hasBytesForTtptr = (InputLength - StartPosition) >= 8ULL;
  uint64_t positionAfterTtptr0;
  uint64_t positionAfterTtptr;
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
  if (hasBytesForTtptr)
  {
    positionAfterTtptr0 = StartPosition + 8ULL;
  }
  else
  {
    positionAfterTtptr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterTtptr0))
  {
    positionAfterTtptr = positionAfterTtptr0;
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
      positionAfterTtptr = positionAfterTtptr0;
    }
    else
    {
      positionAfterTtptr =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTtptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterTtptr))
  {
    return positionAfterTtptr;
  }
  ErrorHandlerFn("_I",
    "ttptr",
    EverParseErrorReasonOfResult(positionAfterTtptr),
    EverParseGetValidatorErrorKind(positionAfterTtptr),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTtptr;
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
  BOOLEAN hasBytesForFst = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterFst0;
  uint64_t res0;
  uint64_t positionAfterFst;
  BOOLEAN hasBytesForSnd;
  uint64_t positionAfterSnd0;
  uint64_t res1;
  uint64_t positionAfterSnd;
  BOOLEAN hasBytesForTag;
  uint64_t positionAfterTag0;
  uint64_t res;
  uint64_t positionAfterTag;
  BOOLEAN hasBytesForTptr1;
  uint64_t positionAfterTptr10;
  uint64_t positionAfterTptr11;
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
  uint64_t positionAfterTptr1;
  BOOLEAN hasBytesForTptr2;
  uint64_t positionAfterTptr20;
  uint64_t positionAfterTptr2;
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
  if (hasBytesForFst)
  {
    positionAfterFst0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterFst0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterFst0))
  {
    res0 = positionAfterFst0;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "fst",
      EverParseErrorReasonOfResult(positionAfterFst0),
      EverParseGetValidatorErrorKind(positionAfterFst0),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterFst0;
  }
  positionAfterFst = res0;
  if (EverParseIsError(positionAfterFst))
  {
    return positionAfterFst;
  }
  /* Validating field snd */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytesForSnd = (InputLength - positionAfterFst) >= 4ULL;
  if (hasBytesForSnd)
  {
    positionAfterSnd0 = positionAfterFst + 4ULL;
  }
  else
  {
    positionAfterSnd0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterFst);
  }
  if (EverParseIsSuccess(positionAfterSnd0))
  {
    res1 = positionAfterSnd0;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "snd",
      EverParseErrorReasonOfResult(positionAfterSnd0),
      EverParseGetValidatorErrorKind(positionAfterSnd0),
      Ctxt,
      Input,
      positionAfterFst);
    res1 = positionAfterSnd0;
  }
  positionAfterSnd = res1;
  if (EverParseIsError(positionAfterSnd))
  {
    return positionAfterSnd;
  }
  /* Validating field tag */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  hasBytesForTag = (InputLength - positionAfterSnd) >= 1ULL;
  if (hasBytesForTag)
  {
    positionAfterTag0 = positionAfterSnd + 1ULL;
  }
  else
  {
    positionAfterTag0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterSnd);
  }
  if (EverParseIsSuccess(positionAfterTag0))
  {
    res = positionAfterTag0;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "tag",
      EverParseErrorReasonOfResult(positionAfterTag0),
      EverParseGetValidatorErrorKind(positionAfterTag0),
      Ctxt,
      Input,
      positionAfterSnd);
    res = positionAfterTag0;
  }
  positionAfterTag = res;
  if (EverParseIsError(positionAfterTag))
  {
    return positionAfterTag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForTptr1 = (InputLength - positionAfterTag) >= 8ULL;
  if (hasBytesForTptr1)
  {
    positionAfterTptr10 = positionAfterTag + 8ULL;
  }
  else
  {
    positionAfterTptr10 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTag);
  }
  if (EverParseIsError(positionAfterTptr10))
  {
    positionAfterTptr11 = positionAfterTptr10;
  }
  else
  {
    tptr1 = Load64Le(Input + (uint32_t)positionAfterTag);
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
        positionAfterTag);
      actionResult = FALSE;
    }
    if (actionResult)
    {
      positionAfterTptr11 = positionAfterTptr10;
    }
    else
    {
      positionAfterTptr11 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTptr10);
    }
  }
  if (EverParseIsSuccess(positionAfterTptr11))
  {
    positionAfterTptr1 = positionAfterTptr11;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "tptr1",
      EverParseErrorReasonOfResult(positionAfterTptr11),
      EverParseGetValidatorErrorKind(positionAfterTptr11),
      Ctxt,
      Input,
      positionAfterTag);
    positionAfterTptr1 = positionAfterTptr11;
  }
  if (EverParseIsError(positionAfterTptr1))
  {
    return positionAfterTptr1;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForTptr2 = (InputLength - positionAfterTptr1) >= 8ULL;
  if (hasBytesForTptr2)
  {
    positionAfterTptr20 = positionAfterTptr1 + 8ULL;
  }
  else
  {
    positionAfterTptr20 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTptr1);
  }
  if (EverParseIsError(positionAfterTptr20))
  {
    positionAfterTptr2 = positionAfterTptr20;
  }
  else
  {
    tptr2 = Load64Le(Input + (uint32_t)positionAfterTptr1);
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
        positionAfterTptr1);
      actionResult0 = FALSE;
    }
    if (actionResult0)
    {
      positionAfterTptr2 = positionAfterTptr20;
    }
    else
    {
      positionAfterTptr2 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTptr20);
    }
  }
  if (EverParseIsSuccess(positionAfterTptr2))
  {
    return positionAfterTptr2;
  }
  ErrorHandlerFn("_MultiProbe",
    "tptr2",
    EverParseErrorReasonOfResult(positionAfterTptr2),
    EverParseGetValidatorErrorKind(positionAfterTptr2),
    Ctxt,
    Input,
    positionAfterTptr1);
  return positionAfterTptr2;
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
  BOOLEAN hasBytesForBound = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterBound0;
  uint64_t positionAfterBound;
  uint32_t bound;
  BOOLEAN hasBytesForPtr;
  uint64_t positionAfterPtr0;
  uint64_t positionAfterPtr;
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
  if (hasBytesForBound)
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
  hasBytesForPtr = (InputLength - positionAfterBound) >= 8ULL;
  if (hasBytesForPtr)
  {
    positionAfterPtr0 = positionAfterBound + 8ULL;
  }
  else
  {
    positionAfterPtr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  if (EverParseIsError(positionAfterPtr0))
  {
    positionAfterPtr = positionAfterPtr0;
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
      positionAfterPtr = positionAfterPtr0;
    }
    else
    {
      positionAfterPtr =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtr0);
    }
  }
  if (EverParseIsSuccess(positionAfterPtr))
  {
    return positionAfterPtr;
  }
  ErrorHandlerFn("_MaybeT",
    "ptr",
    EverParseErrorReasonOfResult(positionAfterPtr),
    EverParseGetValidatorErrorKind(positionAfterPtr),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterPtr;
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
  BOOLEAN hasBytesForBound = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterBound0;
  uint64_t positionAfterBound;
  uint32_t bound;
  BOOLEAN hasBytesForPtr;
  uint64_t positionAfterPtr0;
  uint64_t positionAfterPtr;
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
  if (hasBytesForBound)
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
  hasBytesForPtr = (InputLength - positionAfterBound) >= 4ULL;
  if (hasBytesForPtr)
  {
    positionAfterPtr0 = positionAfterBound + 4ULL;
  }
  else
  {
    positionAfterPtr0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  if (EverParseIsError(positionAfterPtr0))
  {
    positionAfterPtr = positionAfterPtr0;
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
      positionAfterPtr = positionAfterPtr0;
    }
    else
    {
      positionAfterPtr =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtr0);
    }
  }
  if (EverParseIsSuccess(positionAfterPtr))
  {
    return positionAfterPtr;
  }
  ErrorHandlerFn("_CoercePtr",
    "ptr",
    EverParseErrorReasonOfResult(positionAfterPtr),
    EverParseGetValidatorErrorKind(positionAfterPtr),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterPtr;
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
  BOOLEAN hasBytesForXY = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterX;
  if (hasBytesForXY)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterX = res;
  if (EverParseIsSuccess(positionAfterX))
  {
    return positionAfterX;
  }
  ErrorHandlerFn("_ProbeOnly",
    "x",
    EverParseErrorReasonOfResult(positionAfterX),
    EverParseGetValidatorErrorKind(positionAfterX),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX;
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
  BOOLEAN hasBytesForXY = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterX;
  if (hasBytesForXY)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterX = res;
  if (EverParseIsSuccess(positionAfterX))
  {
    return positionAfterX;
  }
  ErrorHandlerFn("_BothEntrypoints",
    "x",
    EverParseErrorReasonOfResult(positionAfterX),
    EverParseGetValidatorErrorKind(positionAfterX),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX;
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
  BOOLEAN hasBytesForXY = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterX;
  if (hasBytesForXY)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterX = res;
  if (EverParseIsSuccess(positionAfterX))
  {
    return positionAfterX;
  }
  ErrorHandlerFn("_NamedPlainEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterX),
    EverParseGetValidatorErrorKind(positionAfterX),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX;
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
  BOOLEAN hasBytesForXY = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterX;
  if (hasBytesForXY)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterX = res;
  if (EverParseIsSuccess(positionAfterX))
  {
    return positionAfterX;
  }
  ErrorHandlerFn("_NamedProbeEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterX),
    EverParseGetValidatorErrorKind(positionAfterX),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX;
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
  BOOLEAN hasBytesForXY = (InputLength - StartPosition) >= 8ULL;
  uint64_t res;
  uint64_t positionAfterX;
  if (hasBytesForXY)
  {
    res = StartPosition + 8ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterX = res;
  if (EverParseIsSuccess(positionAfterX))
  {
    return positionAfterX;
  }
  ErrorHandlerFn("_NamedBothEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterX),
    EverParseGetValidatorErrorKind(positionAfterX),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX;
}

