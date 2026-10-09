

#include "GetFieldPtr.h"

#include "EverParse.h"

uint8_t
GetFieldPtrValidateT(
  uint8_t **Out,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field f1 */
  size_t p1 = *SlPos;
  uint64_t fieldStartT = (uint64_t)p1;
  uint64_t startPositionT = fieldStartT;
  size_t pos0 = (size_t)0U;
  size_t p00 = pos0;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)10U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterT;
  size_t consumed0;
  size_t p3;
  size_t p_;
  uint8_t resultAfterf1;
  size_t p4;
  uint64_t fieldStartT0;
  uint64_t startPositionT0;
  size_t p5;
  uint64_t fieldStartf2;
  size_t p6;
  uint64_t fieldStartT1;
  uint64_t startPositionT1;
  size_t pos;
  size_t p0;
  size_t p7;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res;
  uint8_t resultAfterT0;
  size_t consumed;
  size_t p;
  size_t p_0;
  uint8_t resultAfterf2;
  uint8_t resultAfterT1;
  size_t startPosSz;
  uint8_t *hd;
  BOOLEAN actionSuccessF2;
  if (hasBytes0)
  {
    pos0 = p00 + (size_t)10U;
    res0 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    consumed0 = pos0;
    p3 = *SlPos;
    p_ = p3 + consumed0;
    *SlPos = p_;
    resultAfterT = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterT = res0;
  }
  if (resultAfterT == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterf1 = resultAfterT;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f1",
      EverParseErrorReasonOfResult(resultAfterT),
      resultAfterT,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionT);
    resultAfterf1 = resultAfterT;
  }
  if (resultAfterf1 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    /* Validating field f2 */
    p4 = *SlPos;
    fieldStartT0 = (uint64_t)p4;
    startPositionT0 = fieldStartT0;
    p5 = *SlPos;
    fieldStartf2 = (uint64_t)p5;
    p6 = *SlPos;
    fieldStartT1 = (uint64_t)p6;
    startPositionT1 = fieldStartT1;
    pos = (size_t)0U;
    p0 = pos;
    p7 = *SlPos;
    rem = SlLen - p7;
    hasBytes = p0 <= rem && (size_t)20U <= (rem - p0);
    if (hasBytes)
    {
      pos = p0 + (size_t)20U;
      res = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res == EVERPARSE_VALIDATOR_SUCCESS)
    {
      consumed = pos;
      p = *SlPos;
      p_0 = p + consumed;
      *SlPos = p_0;
      resultAfterT0 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterT0 = res;
    }
    if (resultAfterT0 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      resultAfterf2 = resultAfterT0;
    }
    else
    {
      ErrorHandlerFn("_T",
        "f2.base",
        EverParseErrorReasonOfResult(resultAfterT0),
        resultAfterT0,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        startPositionT1);
      resultAfterf2 = resultAfterT0;
    }
    if (resultAfterf2 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      startPosSz = (size_t)fieldStartf2;
      hd = SlBase + startPosSz;
      *Out = hd;
      actionSuccessF2 = TRUE;
      resultAfterT1 =
        actionSuccessF2 ? EVERPARSE_VALIDATOR_SUCCESS
                        : EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterT1 = resultAfterf2;
    }
    if (resultAfterT1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterT1;
    }
    ErrorHandlerFn("_T",
      "f2",
      EverParseErrorReasonOfResult(resultAfterT1),
      resultAfterT1,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionT0);
    return resultAfterT1;
  }
  return resultAfterf1;
}

uint8_t
GetFieldPtrValidateTact(
  uint8_t **Out,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field f1 */
  size_t p1 = *SlPos;
  uint64_t fieldStartTact = (uint64_t)p1;
  uint64_t startPositionTact = fieldStartTact;
  size_t pos0 = (size_t)0U;
  size_t p00 = pos0;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)10U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterTact;
  size_t consumed0;
  size_t p3;
  size_t p_;
  uint8_t resultAfterf1;
  size_t p4;
  uint64_t fieldStartTact0;
  uint64_t startPositionTact0;
  size_t p5;
  uint64_t fieldStartf2;
  size_t p6;
  uint64_t fieldStartTact1;
  uint64_t startPositionTact1;
  size_t pos;
  size_t p0;
  size_t p7;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res;
  uint8_t resultAfterTact0;
  size_t consumed;
  size_t p;
  size_t p_0;
  uint8_t resultAfterf2;
  uint8_t resultAfterTact1;
  size_t startPosSz;
  uint8_t *hd;
  BOOLEAN actionSuccessF2;
  if (hasBytes0)
  {
    pos0 = p00 + (size_t)10U;
    res0 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    consumed0 = pos0;
    p3 = *SlPos;
    p_ = p3 + consumed0;
    *SlPos = p_;
    resultAfterTact = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterTact = res0;
  }
  if (resultAfterTact == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterf1 = resultAfterTact;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f1",
      EverParseErrorReasonOfResult(resultAfterTact),
      resultAfterTact,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionTact);
    resultAfterf1 = resultAfterTact;
  }
  if (resultAfterf1 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    /* Validating field f2 */
    p4 = *SlPos;
    fieldStartTact0 = (uint64_t)p4;
    startPositionTact0 = fieldStartTact0;
    p5 = *SlPos;
    fieldStartf2 = (uint64_t)p5;
    p6 = *SlPos;
    fieldStartTact1 = (uint64_t)p6;
    startPositionTact1 = fieldStartTact1;
    pos = (size_t)0U;
    p0 = pos;
    p7 = *SlPos;
    rem = SlLen - p7;
    hasBytes = p0 <= rem && (size_t)20U <= (rem - p0);
    if (hasBytes)
    {
      pos = p0 + (size_t)20U;
      res = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res == EVERPARSE_VALIDATOR_SUCCESS)
    {
      consumed = pos;
      p = *SlPos;
      p_0 = p + consumed;
      *SlPos = p_0;
      resultAfterTact0 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterTact0 = res;
    }
    if (resultAfterTact0 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      resultAfterf2 = resultAfterTact0;
    }
    else
    {
      ErrorHandlerFn("_TAct",
        "f2.base",
        EverParseErrorReasonOfResult(resultAfterTact0),
        resultAfterTact0,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        startPositionTact1);
      resultAfterf2 = resultAfterTact0;
    }
    if (resultAfterf2 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      startPosSz = (size_t)fieldStartf2;
      hd = SlBase + startPosSz;
      *Out = hd;
      actionSuccessF2 = TRUE;
      resultAfterTact1 =
        actionSuccessF2 ? EVERPARSE_VALIDATOR_SUCCESS
                        : EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterTact1 = resultAfterf2;
    }
    if (resultAfterTact1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterTact1;
    }
    ErrorHandlerFn("_TAct",
      "f2",
      EverParseErrorReasonOfResult(resultAfterTact1),
      resultAfterTact1,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionTact0);
    return resultAfterTact1;
  }
  return resultAfterf1;
}

