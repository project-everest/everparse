

#include "GetFieldPtr.h"

uint8_t
GetFieldPtrValidateCoreT(
  uint8_t **Out,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field f1 */
  size_t p = SlPos[0U];
  uint64_t fieldStartT = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)10U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterT;
  size_t consumed0;
  size_t p20;
  size_t p_;
  uint8_t resultAfterf1;
  size_t p2;
  uint64_t fieldStartT1;
  size_t p3;
  uint64_t fieldStartf2;
  size_t p4;
  uint64_t fieldStartT2;
  size_t pos1;
  size_t p01;
  size_t p5;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res1;
  uint8_t resultAfterT1;
  size_t consumed;
  size_t p6;
  size_t p_0;
  uint8_t resultAfterf2;
  uint8_t resultAfterT2;
  size_t startPosSz;
  uint8_t *hd;
  if (hasBytes)
  {
    pos = p0 + (size_t)10U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed0 = pos;
    p20 = SlPos[0U];
    p_ = p20 + consumed0;
    SlPos[0U] = p_;
    resultAfterT = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterT = res;
  }
  if (resultAfterT == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterf1 = resultAfterT;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f1",
      EverParsePulseInternalErrorReasonOfResult(resultAfterT),
      resultAfterT == 0U || (resultAfterT >= 2U && resultAfterT <= 8U) ? (uint64_t)(uint32_t)resultAfterT
                                                                       : 15ULL,
      Ctxt,
      SlBase,
      fieldStartT);
    resultAfterf1 = resultAfterT;
  }
  if (resultAfterf1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    /* Validating field f2 */
    p2 = SlPos[0U];
    fieldStartT1 = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStartf2 = (uint64_t)p3;
    p4 = SlPos[0U];
    fieldStartT2 = (uint64_t)p4;
    pos1 = (size_t)0U;
    p01 = pos1;
    p5 = SlPos[0U];
    rem1 = SlLen - p5;
    hasBytes1 = p01 <= rem1 && (size_t)20U <= (rem1 - p01);
    if (hasBytes1)
    {
      pos1 = p01 + (size_t)20U;
      res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed = pos1;
      p6 = SlPos[0U];
      p_0 = p6 + consumed;
      SlPos[0U] = p_0;
      resultAfterT1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterT1 = res1;
    }
    if (resultAfterT1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      resultAfterf2 = resultAfterT1;
    }
    else
    {
      ErrorHandlerFn("_T",
        "f2.base",
        EverParsePulseInternalErrorReasonOfResult(resultAfterT1),
        resultAfterT1 == 0U || (resultAfterT1 >= 2U && resultAfterT1 <= 8U) ? (uint64_t)(uint32_t)resultAfterT1
                                                                            : 15ULL,
        Ctxt,
        SlBase,
        fieldStartT2);
      resultAfterf2 = resultAfterT1;
    }
    if (resultAfterf2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      startPosSz = (size_t)fieldStartf2;
      hd = SlBase + startPosSz;
      Out[0U] = hd;
      resultAfterT2 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterT2 = resultAfterf2;
    }
    if (resultAfterT2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterT2;
    }
    ErrorHandlerFn("_T",
      "f2",
      EverParsePulseInternalErrorReasonOfResult(resultAfterT2),
      resultAfterT2 == 0U || (resultAfterT2 >= 2U && resultAfterT2 <= 8U) ? (uint64_t)(uint32_t)resultAfterT2
                                                                          : 15ULL,
      Ctxt,
      SlBase,
      fieldStartT1);
    return resultAfterT2;
  }
  return resultAfterf1;
}

uint64_t
GetFieldPtrValidateT(
  uint8_t **Out,
  uint8_t *Ctxt,
  void
  (*Handler)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = GetFieldPtrValidateCoreT(Out, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
GetFieldPtrValidateCoreTact(
  uint8_t **Out,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field f1 */
  size_t p = SlPos[0U];
  uint64_t fieldStartTact = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)10U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterTact;
  size_t consumed0;
  size_t p20;
  size_t p_;
  uint8_t resultAfterf1;
  size_t p2;
  uint64_t fieldStartTact1;
  size_t p3;
  uint64_t fieldStartf2;
  size_t p4;
  uint64_t fieldStartTact2;
  size_t pos1;
  size_t p01;
  size_t p5;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res1;
  uint8_t resultAfterTact1;
  size_t consumed;
  size_t p6;
  size_t p_0;
  uint8_t resultAfterf2;
  uint8_t resultAfterTact2;
  size_t startPosSz;
  uint8_t *hd;
  if (hasBytes)
  {
    pos = p0 + (size_t)10U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed0 = pos;
    p20 = SlPos[0U];
    p_ = p20 + consumed0;
    SlPos[0U] = p_;
    resultAfterTact = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterTact = res;
  }
  if (resultAfterTact == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterf1 = resultAfterTact;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f1",
      EverParsePulseInternalErrorReasonOfResult(resultAfterTact),
      resultAfterTact == 0U || (resultAfterTact >= 2U && resultAfterTact <= 8U) ? (uint64_t)(uint32_t)resultAfterTact
                                                                                : 15ULL,
      Ctxt,
      SlBase,
      fieldStartTact);
    resultAfterf1 = resultAfterTact;
  }
  if (resultAfterf1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    /* Validating field f2 */
    p2 = SlPos[0U];
    fieldStartTact1 = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStartf2 = (uint64_t)p3;
    p4 = SlPos[0U];
    fieldStartTact2 = (uint64_t)p4;
    pos1 = (size_t)0U;
    p01 = pos1;
    p5 = SlPos[0U];
    rem1 = SlLen - p5;
    hasBytes1 = p01 <= rem1 && (size_t)20U <= (rem1 - p01);
    if (hasBytes1)
    {
      pos1 = p01 + (size_t)20U;
      res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed = pos1;
      p6 = SlPos[0U];
      p_0 = p6 + consumed;
      SlPos[0U] = p_0;
      resultAfterTact1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterTact1 = res1;
    }
    if (resultAfterTact1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      resultAfterf2 = resultAfterTact1;
    }
    else
    {
      ErrorHandlerFn("_TAct",
        "f2.base",
        EverParsePulseInternalErrorReasonOfResult(resultAfterTact1),
        resultAfterTact1 == 0U || (resultAfterTact1 >= 2U && resultAfterTact1 <= 8U) ? (uint64_t)(uint32_t)resultAfterTact1
                                                                                     : 15ULL,
        Ctxt,
        SlBase,
        fieldStartTact2);
      resultAfterf2 = resultAfterTact1;
    }
    if (resultAfterf2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      startPosSz = (size_t)fieldStartf2;
      hd = SlBase + startPosSz;
      Out[0U] = hd;
      resultAfterTact2 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterTact2 = resultAfterf2;
    }
    if (resultAfterTact2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterTact2;
    }
    ErrorHandlerFn("_TAct",
      "f2",
      EverParsePulseInternalErrorReasonOfResult(resultAfterTact2),
      resultAfterTact2 == 0U || (resultAfterTact2 >= 2U && resultAfterTact2 <= 8U) ? (uint64_t)(uint32_t)resultAfterTact2
                                                                                   : 15ULL,
      Ctxt,
      SlBase,
      fieldStartTact1);
    return resultAfterTact2;
  }
  return resultAfterf1;
}

uint64_t
GetFieldPtrValidateTact(
  uint8_t **Out,
  uint8_t *Ctxt,
  void
  (*Handler)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = GetFieldPtrValidateCoreTact(Out, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

