

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
    BOOLEAN ok = ProbeInit((uint64_t)8U, Dest);
    if (!ok)
    {
      failed = TRUE;
    }
    BOOLEAN hasFailed = failed;
    if (!hasFailed)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      if (rd != 0ULL || wr != 0ULL || (uint64_t)8U == 0ULL)
      {
        failed = TRUE;
      }
      else
      {
        BOOLEAN ok0 = ProbeAndCopy(src64, (uint64_t)8U, Dest);
        if (ok0)
        {
          readOffset = (uint64_t)8U;
          writeOffset = (uint64_t)8U;
        }
        else
        {
          failed = TRUE;
        }
      }
    }
    BOOLEAN hasFailed0 = failed;
    uint64_t b;
    if (hasFailed0)
    {
      b = 0ULL;
    }
    else
    {
      b = writeOffset;
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
    BOOLEAN ok = ProbeInit((uint64_t)9U, DestS);
    if (!ok)
    {
      failed = TRUE;
    }
    BOOLEAN hasFailed = failed;
    if (!hasFailed)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      if (rd != 0ULL || wr != 0ULL || (uint64_t)9U == 0ULL)
      {
        failed = TRUE;
      }
      else
      {
        BOOLEAN ok0 = ProbeAndCopyAlt(src64, (uint64_t)9U, DestS);
        if (ok0)
        {
          readOffset = (uint64_t)9U;
          writeOffset = (uint64_t)9U;
        }
        else
        {
          failed = TRUE;
        }
      }
    }
    BOOLEAN hasFailed0 = failed;
    uint64_t b;
    if (hasFailed0)
    {
      b = 0ULL;
    }
    else
    {
      b = writeOffset;
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
    BOOLEAN ok = ProbeInit((uint64_t)9U, DestS);
    if (!ok)
    {
      failed = TRUE;
    }
    BOOLEAN hasFailed = failed;
    if (!hasFailed)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      if (rd != 0ULL || wr != 0ULL || (uint64_t)9U == 0ULL)
      {
        failed = TRUE;
      }
      else
      {
        BOOLEAN ok0 = ProbeAndCopy(src64, (uint64_t)9U, DestS);
        if (ok0)
        {
          readOffset = (uint64_t)9U;
          writeOffset = (uint64_t)9U;
        }
        else
        {
          failed = TRUE;
        }
      }
    }
    BOOLEAN hasFailed0 = failed;
    uint64_t b;
    if (hasFailed0)
    {
      b = 0ULL;
    }
    else
    {
      b = writeOffset;
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
    BOOLEAN ok = ProbeInit((uint64_t)8U, DestT);
    if (!ok)
    {
      failed = TRUE;
    }
    BOOLEAN hasFailed = failed;
    if (!hasFailed)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      if (rd != 0ULL || wr != 0ULL || (uint64_t)8U == 0ULL)
      {
        failed = TRUE;
      }
      else
      {
        BOOLEAN ok0 = ProbeAndCopyAlt(src64, (uint64_t)8U, DestT);
        if (ok0)
        {
          readOffset = (uint64_t)8U;
          writeOffset = (uint64_t)8U;
        }
        else
        {
          failed = TRUE;
        }
      }
    }
    BOOLEAN hasFailed0 = failed;
    uint64_t b;
    if (hasFailed0)
    {
      b = 0ULL;
    }
    else
    {
      b = writeOffset;
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
    BOOLEAN ok = ProbeInit((uint64_t)8U, DestT);
    if (!ok)
    {
      failed = TRUE;
    }
    BOOLEAN hasFailed = failed;
    if (!hasFailed)
    {
      uint64_t rd = readOffset;
      uint64_t wr = writeOffset;
      if (rd != 0ULL || wr != 0ULL || (uint64_t)8U == 0ULL)
      {
        failed = TRUE;
      }
      else
      {
        BOOLEAN ok0 = ProbeAndCopy(src64, (uint64_t)8U, DestT);
        if (ok0)
        {
          readOffset = (uint64_t)8U;
          writeOffset = (uint64_t)8U;
        }
        else
        {
          failed = TRUE;
        }
      }
    }
    BOOLEAN hasFailed0 = failed;
    uint64_t b;
    if (hasFailed0)
    {
      b = 0ULL;
    }
    else
    {
      b = writeOffset;
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

static void
ProbeTt(
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  EVERPARSE_COPY_BUFFER_T Dest
)
{
  uint64_t rd = *ReadOffset;
  uint64_t wr = *WriteOffset;
  if (rd != 0ULL || wr != 0ULL || (uint64_t)9U == 0ULL)
  {
    *Failed = TRUE;
    return;
  }
  BOOLEAN ok = ProbeAndCopy(Src, (uint64_t)9U, Dest);
  if (ok)
  {
    *ReadOffset = (uint64_t)9U;
    *WriteOffset = (uint64_t)9U;
    return;
  }
  *Failed = TRUE;
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
    BOOLEAN ok = ProbeInit((uint64_t)9U, Dest);
    if (!ok)
    {
      failed = TRUE;
    }
    BOOLEAN hasFailed = failed;
    if (!hasFailed)
    {
      ProbeTt(&readOffset, &writeOffset, &failed, src64, Dest);
    }
    BOOLEAN hasFailed0 = failed;
    uint64_t b;
    if (hasFailed0)
    {
      b = 0ULL;
    }
    else
    {
      b = writeOffset;
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

