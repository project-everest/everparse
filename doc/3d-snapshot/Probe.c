

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
  uint64_t positionAfterX;
  uint64_t positionAfterXOrError;
  uint16_t x;
  BOOLEAN xConstraintIsOk;
  uint64_t positionAfterCheckedX;
  BOOLEAN hasBytesForY_refinement;
  uint64_t positionAfterY_refinement;
  uint64_t positionAfterY_refinementOrError;
  uint16_t y_refinement;
  BOOLEAN y_refinementConstraintIsOk;
  if (hasBytesForX)
  {
    positionAfterX = StartPosition + 2ULL;
  }
  else
  {
    positionAfterX =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterX))
  {
    positionAfterXOrError = positionAfterX;
  }
  else
  {
    x = Load16Le(Input + (uint32_t)StartPosition);
    xConstraintIsOk = (uint32_t)x >= Bound;
    positionAfterCheckedX = EverParseCheckConstraintOk(xConstraintIsOk, positionAfterX);
    if (EverParseIsError(positionAfterCheckedX))
    {
      positionAfterXOrError = positionAfterCheckedX;
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
        positionAfterY_refinementOrError = positionAfterY_refinement;
      }
      else
      {
        /* reading field_value */
        y_refinement = Load16Le(Input + (uint32_t)positionAfterCheckedX);
        /* start: checking constraint */
        y_refinementConstraintIsOk = y_refinement >= x;
        /* end: checking constraint */
        positionAfterY_refinementOrError =
          EverParseCheckConstraintOk(y_refinementConstraintIsOk,
            positionAfterY_refinement);
      }
      if (EverParseIsSuccess(positionAfterY_refinementOrError))
      {
        positionAfterXOrError = positionAfterY_refinementOrError;
      }
      else
      {
        ErrorHandlerFn("_T",
          "y.refinement",
          EverParseErrorReasonOfResult(positionAfterY_refinementOrError),
          EverParseGetValidatorErrorKind(positionAfterY_refinementOrError),
          Ctxt,
          Input,
          positionAfterCheckedX);
        positionAfterXOrError = positionAfterY_refinementOrError;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    return positionAfterXOrError;
  }
  ErrorHandlerFn("_T",
    "x",
    EverParseErrorReasonOfResult(positionAfterXOrError),
    EverParseGetValidatorErrorKind(positionAfterXOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterXOrError;
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
  uint64_t positionAfterBoundOrError;
  uint64_t positionAfterBound;
  uint8_t bound;
  BOOLEAN hasBytesForTpointer;
  uint64_t positionAfterTpointer;
  uint64_t positionAfterTpointerOrError;
  uint64_t tpointer;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForTpointer;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN okForTpointer1;
  uint64_t wr;
  BOOLEAN hasFailedForTpointer;
  uint64_t b;
  BOOLEAN actionResultForTpointer;
  uint64_t result;
  if (hasBytesForBound)
  {
    positionAfterBoundOrError = StartPosition + 1ULL;
  }
  else
  {
    positionAfterBoundOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBoundOrError))
  {
    positionAfterBound = positionAfterBoundOrError;
  }
  else
  {
    ErrorHandlerFn("_S",
      "bound",
      EverParseErrorReasonOfResult(positionAfterBoundOrError),
      EverParseGetValidatorErrorKind(positionAfterBoundOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBound = positionAfterBoundOrError;
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
    positionAfterTpointer = positionAfterBound + 8ULL;
  }
  else
  {
    positionAfterTpointer =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  if (EverParseIsError(positionAfterTpointer))
  {
    positionAfterTpointerOrError = positionAfterTpointer;
  }
  else
  {
    tpointer = Load64Le(Input + (uint32_t)positionAfterBound);
    src64 = tpointer;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    okForTpointer = ProbeInit2("_S.tpointer", (uint64_t)4U, Dest);
    if (okForTpointer)
    {
      rd = readOffset;
      wr0 = writeOffset;
      okForTpointer1 = ProbeAndCopy2((uint64_t)4U, rd, wr0, src64, Dest);
      if (okForTpointer1)
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
    hasFailedForTpointer = failed;
    if (hasFailedForTpointer)
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
      actionResultForTpointer = !EverParseIsError(result);
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
      actionResultForTpointer = FALSE;
    }
    if (actionResultForTpointer)
    {
      positionAfterTpointerOrError = positionAfterTpointer;
    }
    else
    {
      positionAfterTpointerOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTpointer);
    }
  }
  if (EverParseIsSuccess(positionAfterTpointerOrError))
  {
    return positionAfterTpointerOrError;
  }
  ErrorHandlerFn("_S",
    "tpointer",
    EverParseErrorReasonOfResult(positionAfterTpointerOrError),
    EverParseGetValidatorErrorKind(positionAfterTpointerOrError),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterTpointerOrError;
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
  uint64_t positionAfterTagOrError;
  uint64_t resForTag;
  uint64_t positionAfterTag;
  BOOLEAN hasBytesForSpointer;
  uint64_t positionAfterSpointer;
  uint64_t positionAfterSpointerOrError;
  uint64_t spointer;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForSpointer;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN okForSpointer1;
  uint64_t wr;
  BOOLEAN hasFailedForSpointer;
  uint64_t b;
  BOOLEAN actionResultForSpointer;
  uint64_t result;
  if (hasBytesForTag)
  {
    positionAfterTagOrError = StartPosition + 1ULL;
  }
  else
  {
    positionAfterTagOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterTagOrError))
  {
    resForTag = positionAfterTagOrError;
  }
  else
  {
    ErrorHandlerFn("_U",
      "tag",
      EverParseErrorReasonOfResult(positionAfterTagOrError),
      EverParseGetValidatorErrorKind(positionAfterTagOrError),
      Ctxt,
      Input,
      StartPosition);
    resForTag = positionAfterTagOrError;
  }
  positionAfterTag = resForTag;
  if (EverParseIsError(positionAfterTag))
  {
    return positionAfterTag;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForSpointer = (InputLength - positionAfterTag) >= 8ULL;
  if (hasBytesForSpointer)
  {
    positionAfterSpointer = positionAfterTag + 8ULL;
  }
  else
  {
    positionAfterSpointer =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTag);
  }
  if (EverParseIsError(positionAfterSpointer))
  {
    positionAfterSpointerOrError = positionAfterSpointer;
  }
  else
  {
    spointer = Load64Le(Input + (uint32_t)positionAfterTag);
    src64 = spointer;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    okForSpointer = ProbeInit2("_U.spointer", (uint64_t)9U, DestS);
    if (okForSpointer)
    {
      rd = readOffset;
      wr0 = writeOffset;
      okForSpointer1 = ProbeAndCopy2((uint64_t)9U, rd, wr0, src64, DestS);
      if (okForSpointer1)
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
    hasFailedForSpointer = failed;
    if (hasFailedForSpointer)
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
      actionResultForSpointer = !EverParseIsError(result);
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
      actionResultForSpointer = FALSE;
    }
    if (actionResultForSpointer)
    {
      positionAfterSpointerOrError = positionAfterSpointer;
    }
    else
    {
      positionAfterSpointerOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterSpointer);
    }
  }
  if (EverParseIsSuccess(positionAfterSpointerOrError))
  {
    return positionAfterSpointerOrError;
  }
  ErrorHandlerFn("_U",
    "spointer",
    EverParseErrorReasonOfResult(positionAfterSpointerOrError),
    EverParseGetValidatorErrorKind(positionAfterSpointerOrError),
    Ctxt,
    Input,
    positionAfterTag);
  return positionAfterSpointerOrError;
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
  uint64_t positionAfterTagOrError;
  uint64_t positionAfterTag;
  uint8_t tag;
  BOOLEAN hasBytesForSptr;
  uint64_t positionAfterSptr0;
  uint64_t positionAfterSptrOrError;
  uint64_t sptr;
  uint64_t src640;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed0;
  BOOLEAN okForSptr;
  uint64_t rd0;
  uint64_t wr0;
  BOOLEAN okForSptr1;
  uint64_t wr1;
  BOOLEAN hasFailedForSptr;
  uint64_t b0;
  BOOLEAN actionResultForSptr;
  uint64_t result0;
  uint64_t positionAfterSptr;
  BOOLEAN hasBytesForTptr;
  uint64_t positionAfterTptr0;
  uint64_t positionAfterTptrOrError;
  uint64_t tptr;
  uint64_t src641;
  uint64_t readOffset0;
  uint64_t writeOffset0;
  BOOLEAN failed1;
  BOOLEAN okForTptr;
  uint64_t rd1;
  uint64_t wr2;
  BOOLEAN okForTptr1;
  uint64_t wr3;
  BOOLEAN hasFailedForTptr;
  uint64_t b1;
  BOOLEAN actionResultForTptr;
  uint64_t result1;
  uint64_t positionAfterTptr;
  BOOLEAN hasBytesForT2ptr;
  uint64_t positionAfterT2ptr;
  uint64_t positionAfterT2ptrOrError;
  uint64_t t2ptr;
  uint64_t src64;
  uint64_t readOffset1;
  uint64_t writeOffset1;
  BOOLEAN failed;
  BOOLEAN okForT2ptr;
  uint64_t rd;
  uint64_t wr4;
  BOOLEAN okForT2ptr1;
  uint64_t wr;
  BOOLEAN hasFailedForT2ptr;
  uint64_t b;
  BOOLEAN actionResultForT2ptr;
  uint64_t result;
  if (hasBytesForTag)
  {
    positionAfterTagOrError = StartPosition + 1ULL;
  }
  else
  {
    positionAfterTagOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterTagOrError))
  {
    positionAfterTag = positionAfterTagOrError;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tag",
      EverParseErrorReasonOfResult(positionAfterTagOrError),
      EverParseGetValidatorErrorKind(positionAfterTagOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterTag = positionAfterTagOrError;
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
    positionAfterSptrOrError = positionAfterSptr0;
  }
  else
  {
    sptr = Load64Le(Input + (uint32_t)positionAfterTag);
    src640 = sptr;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed0 = FALSE;
    okForSptr = ProbeInit2("_V.sptr", (uint64_t)9U, DestS);
    if (okForSptr)
    {
      rd0 = readOffset;
      wr0 = writeOffset;
      okForSptr1 = ProbeAndCopy2((uint64_t)9U, rd0, wr0, src640, DestS);
      if (okForSptr1)
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
    hasFailedForSptr = failed0;
    if (hasFailedForSptr)
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
      actionResultForSptr = !EverParseIsError(result0);
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
      actionResultForSptr = FALSE;
    }
    if (actionResultForSptr)
    {
      positionAfterSptrOrError = positionAfterSptr0;
    }
    else
    {
      positionAfterSptrOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterSptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterSptrOrError))
  {
    positionAfterSptr = positionAfterSptrOrError;
  }
  else
  {
    ErrorHandlerFn("_V",
      "sptr",
      EverParseErrorReasonOfResult(positionAfterSptrOrError),
      EverParseGetValidatorErrorKind(positionAfterSptrOrError),
      Ctxt,
      Input,
      positionAfterTag);
    positionAfterSptr = positionAfterSptrOrError;
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
    positionAfterTptrOrError = positionAfterTptr0;
  }
  else
  {
    tptr = Load64Le(Input + (uint32_t)positionAfterSptr);
    src641 = tptr;
    readOffset0 = 0ULL;
    writeOffset0 = 0ULL;
    failed1 = FALSE;
    okForTptr = ProbeInit2("_V.tptr", (uint64_t)8U, DestT);
    if (okForTptr)
    {
      rd1 = readOffset0;
      wr2 = writeOffset0;
      okForTptr1 = ProbeAndCopy2((uint64_t)8U, rd1, wr2, src641, DestT);
      if (okForTptr1)
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
    hasFailedForTptr = failed1;
    if (hasFailedForTptr)
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
      actionResultForTptr = !EverParseIsError(result1);
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
      actionResultForTptr = FALSE;
    }
    if (actionResultForTptr)
    {
      positionAfterTptrOrError = positionAfterTptr0;
    }
    else
    {
      positionAfterTptrOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTptr0);
    }
  }
  if (EverParseIsSuccess(positionAfterTptrOrError))
  {
    positionAfterTptr = positionAfterTptrOrError;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tptr",
      EverParseErrorReasonOfResult(positionAfterTptrOrError),
      EverParseGetValidatorErrorKind(positionAfterTptrOrError),
      Ctxt,
      Input,
      positionAfterSptr);
    positionAfterTptr = positionAfterTptrOrError;
  }
  if (EverParseIsError(positionAfterTptr))
  {
    return positionAfterTptr;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForT2ptr = (InputLength - positionAfterTptr) >= 8ULL;
  if (hasBytesForT2ptr)
  {
    positionAfterT2ptr = positionAfterTptr + 8ULL;
  }
  else
  {
    positionAfterT2ptr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTptr);
  }
  if (EverParseIsError(positionAfterT2ptr))
  {
    positionAfterT2ptrOrError = positionAfterT2ptr;
  }
  else
  {
    t2ptr = Load64Le(Input + (uint32_t)positionAfterTptr);
    src64 = t2ptr;
    readOffset1 = 0ULL;
    writeOffset1 = 0ULL;
    failed = FALSE;
    okForT2ptr = ProbeInit2("_V.t2ptr", (uint64_t)8U, DestT);
    if (okForT2ptr)
    {
      rd = readOffset1;
      wr4 = writeOffset1;
      okForT2ptr1 = ProbeAndCopy2((uint64_t)8U, rd, wr4, src64, DestT);
      if (okForT2ptr1)
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
    hasFailedForT2ptr = failed;
    if (hasFailedForT2ptr)
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
      actionResultForT2ptr = !EverParseIsError(result);
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
      actionResultForT2ptr = FALSE;
    }
    if (actionResultForT2ptr)
    {
      positionAfterT2ptrOrError = positionAfterT2ptr;
    }
    else
    {
      positionAfterT2ptrOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterT2ptr);
    }
  }
  if (EverParseIsSuccess(positionAfterT2ptrOrError))
  {
    return positionAfterT2ptrOrError;
  }
  ErrorHandlerFn("_V",
    "t2ptr",
    EverParseErrorReasonOfResult(positionAfterT2ptrOrError),
    EverParseGetValidatorErrorKind(positionAfterT2ptrOrError),
    Ctxt,
    Input,
    positionAfterTptr);
  return positionAfterT2ptrOrError;
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
  uint64_t resForFstSndTag;
  uint64_t positionAfterFstOrError;
  if (hasBytesForFstSndTag)
  {
    resForFstSndTag = StartPosition + 9ULL;
  }
  else
  {
    resForFstSndTag =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterFstOrError = resForFstSndTag;
  if (EverParseIsSuccess(positionAfterFstOrError))
  {
    return positionAfterFstOrError;
  }
  ErrorHandlerFn("_Indirect",
    "fst",
    EverParseErrorReasonOfResult(positionAfterFstOrError),
    EverParseGetValidatorErrorKind(positionAfterFstOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterFstOrError;
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
  uint64_t resForFstSndTag;
  uint64_t positionAfterFstOrError;
  if (hasBytesForFstSndTag)
  {
    resForFstSndTag = StartPosition + 9ULL;
  }
  else
  {
    resForFstSndTag =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterFstOrError = resForFstSndTag;
  if (EverParseIsSuccess(positionAfterFstOrError))
  {
    return positionAfterFstOrError;
  }
  ErrorHandlerFn("_TT",
    "fst",
    EverParseErrorReasonOfResult(positionAfterFstOrError),
    EverParseGetValidatorErrorKind(positionAfterFstOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterFstOrError;
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
  uint64_t positionAfterTtptr;
  uint64_t positionAfterTtptrOrError;
  uint64_t ttptr;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForTtptr;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN okForTtptr1;
  uint64_t wr;
  BOOLEAN hasFailedForTtptr;
  uint64_t b;
  BOOLEAN actionResultForTtptr;
  uint64_t result;
  if (hasBytesForTtptr)
  {
    positionAfterTtptr = StartPosition + 8ULL;
  }
  else
  {
    positionAfterTtptr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsError(positionAfterTtptr))
  {
    positionAfterTtptrOrError = positionAfterTtptr;
  }
  else
  {
    ttptr = Load64Le(Input + (uint32_t)StartPosition);
    src64 = ttptr;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    okForTtptr = ProbeInit2("_I.ttptr", (uint64_t)9U, Dest);
    if (okForTtptr)
    {
      rd = readOffset;
      wr0 = writeOffset;
      okForTtptr1 = ProbeAndCopy2((uint64_t)9U, rd, wr0, src64, Dest);
      if (okForTtptr1)
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
    hasFailedForTtptr = failed;
    if (hasFailedForTtptr)
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
      actionResultForTtptr = !EverParseIsError(result);
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
      actionResultForTtptr = FALSE;
    }
    if (actionResultForTtptr)
    {
      positionAfterTtptrOrError = positionAfterTtptr;
    }
    else
    {
      positionAfterTtptrOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTtptr);
    }
  }
  if (EverParseIsSuccess(positionAfterTtptrOrError))
  {
    return positionAfterTtptrOrError;
  }
  ErrorHandlerFn("_I",
    "ttptr",
    EverParseErrorReasonOfResult(positionAfterTtptrOrError),
    EverParseGetValidatorErrorKind(positionAfterTtptrOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTtptrOrError;
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
  uint64_t positionAfterFstOrError;
  uint64_t resForFst;
  uint64_t positionAfterFst;
  BOOLEAN hasBytesForSnd;
  uint64_t positionAfterSndOrError;
  uint64_t resForSnd;
  uint64_t positionAfterSnd;
  BOOLEAN hasBytesForTag;
  uint64_t positionAfterTagOrError;
  uint64_t resForTag;
  uint64_t positionAfterTag;
  BOOLEAN hasBytesForTptr1;
  uint64_t positionAfterTptr10;
  uint64_t positionAfterTptr1OrError;
  uint64_t tptr1;
  uint64_t src640;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed0;
  BOOLEAN okForTptr1;
  uint64_t rd0;
  uint64_t wr0;
  BOOLEAN okForTptr11;
  uint64_t wr1;
  BOOLEAN hasFailedForTptr1;
  uint64_t b0;
  BOOLEAN actionResultForTptr1;
  uint64_t result0;
  uint64_t positionAfterTptr1;
  BOOLEAN hasBytesForTptr2;
  uint64_t positionAfterTptr2;
  uint64_t positionAfterTptr2OrError;
  uint64_t tptr2;
  uint64_t src64;
  uint64_t readOffset0;
  uint64_t writeOffset0;
  BOOLEAN failed;
  BOOLEAN okForTptr2;
  uint64_t rd;
  uint64_t wr2;
  BOOLEAN okForTptr21;
  uint64_t wr;
  BOOLEAN hasFailedForTptr2;
  uint64_t b;
  BOOLEAN actionResultForTptr2;
  uint64_t result;
  if (hasBytesForFst)
  {
    positionAfterFstOrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterFstOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterFstOrError))
  {
    resForFst = positionAfterFstOrError;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "fst",
      EverParseErrorReasonOfResult(positionAfterFstOrError),
      EverParseGetValidatorErrorKind(positionAfterFstOrError),
      Ctxt,
      Input,
      StartPosition);
    resForFst = positionAfterFstOrError;
  }
  positionAfterFst = resForFst;
  if (EverParseIsError(positionAfterFst))
  {
    return positionAfterFst;
  }
  /* Validating field snd */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  hasBytesForSnd = (InputLength - positionAfterFst) >= 4ULL;
  if (hasBytesForSnd)
  {
    positionAfterSndOrError = positionAfterFst + 4ULL;
  }
  else
  {
    positionAfterSndOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterFst);
  }
  if (EverParseIsSuccess(positionAfterSndOrError))
  {
    resForSnd = positionAfterSndOrError;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "snd",
      EverParseErrorReasonOfResult(positionAfterSndOrError),
      EverParseGetValidatorErrorKind(positionAfterSndOrError),
      Ctxt,
      Input,
      positionAfterFst);
    resForSnd = positionAfterSndOrError;
  }
  positionAfterSnd = resForSnd;
  if (EverParseIsError(positionAfterSnd))
  {
    return positionAfterSnd;
  }
  /* Validating field tag */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  hasBytesForTag = (InputLength - positionAfterSnd) >= 1ULL;
  if (hasBytesForTag)
  {
    positionAfterTagOrError = positionAfterSnd + 1ULL;
  }
  else
  {
    positionAfterTagOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterSnd);
  }
  if (EverParseIsSuccess(positionAfterTagOrError))
  {
    resForTag = positionAfterTagOrError;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "tag",
      EverParseErrorReasonOfResult(positionAfterTagOrError),
      EverParseGetValidatorErrorKind(positionAfterTagOrError),
      Ctxt,
      Input,
      positionAfterSnd);
    resForTag = positionAfterTagOrError;
  }
  positionAfterTag = resForTag;
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
    positionAfterTptr1OrError = positionAfterTptr10;
  }
  else
  {
    tptr1 = Load64Le(Input + (uint32_t)positionAfterTag);
    src640 = tptr1;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed0 = FALSE;
    okForTptr1 = ProbeInit2("_MultiProbe.tptr1", (uint64_t)4U, DestT1);
    if (okForTptr1)
    {
      rd0 = readOffset;
      wr0 = writeOffset;
      okForTptr11 = ProbeAndCopy2((uint64_t)4U, rd0, wr0, src640, DestT1);
      if (okForTptr11)
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
    hasFailedForTptr1 = failed0;
    if (hasFailedForTptr1)
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
      actionResultForTptr1 = !EverParseIsError(result0);
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
      actionResultForTptr1 = FALSE;
    }
    if (actionResultForTptr1)
    {
      positionAfterTptr1OrError = positionAfterTptr10;
    }
    else
    {
      positionAfterTptr1OrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTptr10);
    }
  }
  if (EverParseIsSuccess(positionAfterTptr1OrError))
  {
    positionAfterTptr1 = positionAfterTptr1OrError;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "tptr1",
      EverParseErrorReasonOfResult(positionAfterTptr1OrError),
      EverParseGetValidatorErrorKind(positionAfterTptr1OrError),
      Ctxt,
      Input,
      positionAfterTag);
    positionAfterTptr1 = positionAfterTptr1OrError;
  }
  if (EverParseIsError(positionAfterTptr1))
  {
    return positionAfterTptr1;
  }
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  hasBytesForTptr2 = (InputLength - positionAfterTptr1) >= 8ULL;
  if (hasBytesForTptr2)
  {
    positionAfterTptr2 = positionAfterTptr1 + 8ULL;
  }
  else
  {
    positionAfterTptr2 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTptr1);
  }
  if (EverParseIsError(positionAfterTptr2))
  {
    positionAfterTptr2OrError = positionAfterTptr2;
  }
  else
  {
    tptr2 = Load64Le(Input + (uint32_t)positionAfterTptr1);
    src64 = tptr2;
    readOffset0 = 0ULL;
    writeOffset0 = 0ULL;
    failed = FALSE;
    okForTptr2 = ProbeInit2("_MultiProbe.tptr2", (uint64_t)4U, DestT2);
    if (okForTptr2)
    {
      rd = readOffset0;
      wr2 = writeOffset0;
      okForTptr21 = ProbeAndCopyAlt((uint64_t)4U, rd, wr2, src64, DestT2);
      if (okForTptr21)
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
    hasFailedForTptr2 = failed;
    if (hasFailedForTptr2)
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
      actionResultForTptr2 = !EverParseIsError(result);
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
      actionResultForTptr2 = FALSE;
    }
    if (actionResultForTptr2)
    {
      positionAfterTptr2OrError = positionAfterTptr2;
    }
    else
    {
      positionAfterTptr2OrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterTptr2);
    }
  }
  if (EverParseIsSuccess(positionAfterTptr2OrError))
  {
    return positionAfterTptr2OrError;
  }
  ErrorHandlerFn("_MultiProbe",
    "tptr2",
    EverParseErrorReasonOfResult(positionAfterTptr2OrError),
    EverParseGetValidatorErrorKind(positionAfterTptr2OrError),
    Ctxt,
    Input,
    positionAfterTptr1);
  return positionAfterTptr2OrError;
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
  uint64_t positionAfterBoundOrError;
  uint64_t positionAfterBound;
  uint32_t bound;
  BOOLEAN hasBytesForPtr;
  uint64_t positionAfterPtr;
  uint64_t positionAfterPtrOrError;
  uint64_t ptr;
  uint64_t src64;
  BOOLEAN actionResultForPtr;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForPtr;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN okForPtr1;
  uint64_t wr;
  BOOLEAN hasFailedForPtr;
  uint64_t b;
  uint64_t result;
  if (hasBytesForBound)
  {
    positionAfterBoundOrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterBoundOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBoundOrError))
  {
    positionAfterBound = positionAfterBoundOrError;
  }
  else
  {
    ErrorHandlerFn("_MaybeT",
      "Bound",
      EverParseErrorReasonOfResult(positionAfterBoundOrError),
      EverParseGetValidatorErrorKind(positionAfterBoundOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBound = positionAfterBoundOrError;
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
    positionAfterPtr = positionAfterBound + 8ULL;
  }
  else
  {
    positionAfterPtr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  if (EverParseIsError(positionAfterPtr))
  {
    positionAfterPtrOrError = positionAfterPtr;
  }
  else
  {
    ptr = Load64Le(Input + (uint32_t)positionAfterBound);
    src64 = ptr;
    if (src64 == 0ULL)
    {
      actionResultForPtr = TRUE;
    }
    else
    {
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      okForPtr = ProbeInit2("_MaybeT.ptr", (uint64_t)4U, Dest);
      if (okForPtr)
      {
        rd = readOffset;
        wr0 = writeOffset;
        okForPtr1 = ProbeAndCopy2((uint64_t)4U, rd, wr0, src64, Dest);
        if (okForPtr1)
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
      hasFailedForPtr = failed;
      if (hasFailedForPtr)
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
        actionResultForPtr = !EverParseIsError(result);
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
        actionResultForPtr = FALSE;
      }
    }
    if (actionResultForPtr)
    {
      positionAfterPtrOrError = positionAfterPtr;
    }
    else
    {
      positionAfterPtrOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtr);
    }
  }
  if (EverParseIsSuccess(positionAfterPtrOrError))
  {
    return positionAfterPtrOrError;
  }
  ErrorHandlerFn("_MaybeT",
    "ptr",
    EverParseErrorReasonOfResult(positionAfterPtrOrError),
    EverParseGetValidatorErrorKind(positionAfterPtrOrError),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterPtrOrError;
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
  uint64_t positionAfterBoundOrError;
  uint64_t positionAfterBound;
  uint32_t bound;
  BOOLEAN hasBytesForPtr;
  uint64_t positionAfterPtr;
  uint64_t positionAfterPtrOrError;
  uint32_t ptr;
  uint64_t src64;
  uint64_t readOffset;
  uint64_t writeOffset;
  BOOLEAN failed;
  BOOLEAN okForPtr;
  uint64_t rd;
  uint64_t wr0;
  BOOLEAN okForPtr1;
  uint64_t wr;
  BOOLEAN hasFailedForPtr;
  uint64_t b;
  BOOLEAN actionResultForPtr;
  uint64_t result;
  if (hasBytesForBound)
  {
    positionAfterBoundOrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterBoundOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBoundOrError))
  {
    positionAfterBound = positionAfterBoundOrError;
  }
  else
  {
    ErrorHandlerFn("_CoercePtr",
      "Bound",
      EverParseErrorReasonOfResult(positionAfterBoundOrError),
      EverParseGetValidatorErrorKind(positionAfterBoundOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBound = positionAfterBoundOrError;
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
    positionAfterPtr = positionAfterBound + 4ULL;
  }
  else
  {
    positionAfterPtr =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBound);
  }
  if (EverParseIsError(positionAfterPtr))
  {
    positionAfterPtrOrError = positionAfterPtr;
  }
  else
  {
    ptr = Load32Le(Input + (uint32_t)positionAfterBound);
    src64 = UlongToPtr2(ptr);
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    okForPtr = ProbeInit2("_CoercePtr.ptr", (uint64_t)4U, Dest);
    if (okForPtr)
    {
      rd = readOffset;
      wr0 = writeOffset;
      okForPtr1 = ProbeAndCopy2((uint64_t)4U, rd, wr0, src64, Dest);
      if (okForPtr1)
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
    hasFailedForPtr = failed;
    if (hasFailedForPtr)
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
      actionResultForPtr = !EverParseIsError(result);
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
      actionResultForPtr = FALSE;
    }
    if (actionResultForPtr)
    {
      positionAfterPtrOrError = positionAfterPtr;
    }
    else
    {
      positionAfterPtrOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED,
          positionAfterPtr);
    }
  }
  if (EverParseIsSuccess(positionAfterPtrOrError))
  {
    return positionAfterPtrOrError;
  }
  ErrorHandlerFn("_CoercePtr",
    "ptr",
    EverParseErrorReasonOfResult(positionAfterPtrOrError),
    EverParseGetValidatorErrorKind(positionAfterPtrOrError),
    Ctxt,
    Input,
    positionAfterBound);
  return positionAfterPtrOrError;
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
  uint64_t resForXY;
  uint64_t positionAfterXOrError;
  if (hasBytesForXY)
  {
    resForXY = StartPosition + 8ULL;
  }
  else
  {
    resForXY =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterXOrError = resForXY;
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    return positionAfterXOrError;
  }
  ErrorHandlerFn("_ProbeOnly",
    "x",
    EverParseErrorReasonOfResult(positionAfterXOrError),
    EverParseGetValidatorErrorKind(positionAfterXOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterXOrError;
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
  uint64_t resForXY;
  uint64_t positionAfterXOrError;
  if (hasBytesForXY)
  {
    resForXY = StartPosition + 8ULL;
  }
  else
  {
    resForXY =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterXOrError = resForXY;
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    return positionAfterXOrError;
  }
  ErrorHandlerFn("_BothEntrypoints",
    "x",
    EverParseErrorReasonOfResult(positionAfterXOrError),
    EverParseGetValidatorErrorKind(positionAfterXOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterXOrError;
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
  uint64_t resForXY;
  uint64_t positionAfterXOrError;
  if (hasBytesForXY)
  {
    resForXY = StartPosition + 8ULL;
  }
  else
  {
    resForXY =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterXOrError = resForXY;
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    return positionAfterXOrError;
  }
  ErrorHandlerFn("_NamedPlainEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterXOrError),
    EverParseGetValidatorErrorKind(positionAfterXOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterXOrError;
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
  uint64_t resForXY;
  uint64_t positionAfterXOrError;
  if (hasBytesForXY)
  {
    resForXY = StartPosition + 8ULL;
  }
  else
  {
    resForXY =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterXOrError = resForXY;
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    return positionAfterXOrError;
  }
  ErrorHandlerFn("_NamedProbeEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterXOrError),
    EverParseGetValidatorErrorKind(positionAfterXOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterXOrError;
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
  uint64_t resForXY;
  uint64_t positionAfterXOrError;
  if (hasBytesForXY)
  {
    resForXY = StartPosition + 8ULL;
  }
  else
  {
    resForXY =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterXOrError = resForXY;
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    return positionAfterXOrError;
  }
  ErrorHandlerFn("_NamedBothEp",
    "x",
    EverParseErrorReasonOfResult(positionAfterXOrError),
    EverParseGetValidatorErrorKind(positionAfterXOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterXOrError;
}

