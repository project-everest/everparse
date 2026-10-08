

#include "GetFieldPtr.h"

#include "EverParse.h"

uint8_t
GetFieldPtrValidateT(
  uint8_t **Out,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
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
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    consumed0 = pos;
    p20 = SlPos[0U];
    p_ = p20 + consumed0;
    SlPos[0U] = p_;
    resultAfterT = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterT = res;
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
      fieldStartT);
    resultAfterf1 = resultAfterT;
  }
  if (resultAfterf1 == EVERPARSE_VALIDATOR_SUCCESS)
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
      res1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      consumed = pos1;
      p6 = SlPos[0U];
      p_0 = p6 + consumed;
      SlPos[0U] = p_0;
      resultAfterT1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterT1 = res1;
    }
    if (resultAfterT1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      resultAfterf2 = resultAfterT1;
    }
    else
    {
      ErrorHandlerFn("_T",
        "f2.base",
        EverParseErrorReasonOfResult(resultAfterT1),
        resultAfterT1,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        fieldStartT2);
      resultAfterf2 = resultAfterT1;
    }
    if (resultAfterf2 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      startPosSz = (size_t)fieldStartf2;
      hd = SlBase + startPosSz;
      Out[0U] = hd;
      resultAfterT2 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterT2 = resultAfterf2;
    }
    if (resultAfterT2 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterT2;
    }
    ErrorHandlerFn("_T",
      "f2",
      EverParseErrorReasonOfResult(resultAfterT2),
      resultAfterT2,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartT1);
    return resultAfterT2;
  }
  return resultAfterf1;
}

uint8_t
GetFieldPtrValidateTact(
  uint8_t **Out,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
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
    res = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSE_VALIDATOR_SUCCESS)
  {
    consumed0 = pos;
    p20 = SlPos[0U];
    p_ = p20 + consumed0;
    SlPos[0U] = p_;
    resultAfterTact = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterTact = res;
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
      fieldStartTact);
    resultAfterf1 = resultAfterTact;
  }
  if (resultAfterf1 == EVERPARSE_VALIDATOR_SUCCESS)
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
      res1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      consumed = pos1;
      p6 = SlPos[0U];
      p_0 = p6 + consumed;
      SlPos[0U] = p_0;
      resultAfterTact1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterTact1 = res1;
    }
    if (resultAfterTact1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      resultAfterf2 = resultAfterTact1;
    }
    else
    {
      ErrorHandlerFn("_TAct",
        "f2.base",
        EverParseErrorReasonOfResult(resultAfterTact1),
        resultAfterTact1,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        fieldStartTact2);
      resultAfterf2 = resultAfterTact1;
    }
    if (resultAfterf2 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      startPosSz = (size_t)fieldStartf2;
      hd = SlBase + startPosSz;
      Out[0U] = hd;
      resultAfterTact2 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterTact2 = resultAfterf2;
    }
    if (resultAfterTact2 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterTact2;
    }
    ErrorHandlerFn("_TAct",
      "f2",
      EverParseErrorReasonOfResult(resultAfterTact2),
      resultAfterTact2,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartTact1);
    return resultAfterTact2;
  }
  return resultAfterf1;
}

