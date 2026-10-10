

#include "Probe.h"

#include "Probe_ExternalAPI.h"

inline uint8_t
ProbeValidateCoreT(
  uint32_t Bound,
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
  size_t p = SlPos[0U];
  uint64_t fieldStartT = (uint64_t)p;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)2U <= (rem - p0);
  uint8_t resultAfterx;
  uint8_t resultAfterT;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  uint8_t first1;
  uint16_t n;
  uint16_t bfirst;
  uint16_t x;
  BOOLEAN xConstraintIsOk;
  size_t p2;
  uint64_t fieldStartT1;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAftery_refinement;
  uint8_t resultAfterT0;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  uint8_t first2;
  uint8_t first3;
  uint16_t n1;
  uint16_t bfirst1;
  uint16_t y_refinement;
  BOOLEAN y_refinementConstraintIsOk;
  if (hasBytes)
  {
    pos = p0 + (size_t)2U;
    resultAfterx = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterx = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterx == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)2U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    first = sub[0U];
    first1 = sub[1U];
    n = (uint16_t)(uint32_t)first1;
    bfirst = (uint16_t)(uint32_t)first;
    x = (uint32_t)bfirst + (uint32_t)n * 256U;
    xConstraintIsOk = (uint32_t)x >= Bound;
    if (xConstraintIsOk)
    {
      /* Validating field y */
      p2 = SlPos[0U];
      fieldStartT1 = (uint64_t)p2;
      pos1 = (size_t)0U;
      /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
      p02 = pos1;
      p3 = SlPos[0U];
      rem1 = SlLen - p3;
      hasBytes1 = p02 <= rem1 && (size_t)2U <= (rem1 - p02);
      if (hasBytes1)
      {
        pos1 = p02 + (size_t)2U;
        resultAftery_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAftery_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (resultAftery_refinement == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        /* reading field_value */
        p03 = SlPos[0U];
        m1 = p03 + (size_t)2U;
        sub1 = SlBase + p03;
        SlPos[0U] = m1;
        first2 = sub1[0U];
        first3 = sub1[1U];
        n1 = (uint16_t)(uint32_t)first3;
        bfirst1 = (uint16_t)(uint32_t)first2;
        y_refinement = (uint32_t)bfirst1 + (uint32_t)n1 * 256U;
        /* start: checking constraint */
        y_refinementConstraintIsOk = y_refinement >= x;
        /* end: checking constraint */
        resultAfterT0 =
          y_refinementConstraintIsOk ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                                     : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
      else
      {
        resultAfterT0 = resultAftery_refinement;
      }
      if (resultAfterT0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        resultAfterT = resultAfterT0;
      }
      else
      {
        ErrorHandlerFn("_T",
          "y.refinement",
          EverParsePulseInternalErrorReasonOfResult(resultAfterT0),
          resultAfterT0 == 0U || (resultAfterT0 >= 2U && resultAfterT0 <= 8U) ? (uint64_t)(uint32_t)resultAfterT0
                                                                              : 15ULL,
          Ctxt,
          SlBase,
          fieldStartT1);
        resultAfterT = resultAfterT0;
      }
    }
    else
    {
      resultAfterT = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
  }
  else
  {
    resultAfterT = resultAfterx;
  }
  if (resultAfterT == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterT;
  }
  ErrorHandlerFn("_T",
    "x",
    EverParsePulseInternalErrorReasonOfResult(resultAfterT),
    resultAfterT == 0U || (resultAfterT >= 2U && resultAfterT <= 8U) ? (uint64_t)(uint32_t)resultAfterT
                                                                     : 15ULL,
    Ctxt,
    SlBase,
    fieldStartT);
  return resultAfterT;
}

uint8_t
ProbeValidateCoreS(
  EVERPARSE_COPY_BUFFER_T Dest,
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
  size_t pos = (size_t)0U;
  size_t p = SlPos[0U];
  uint64_t viewStart = (uint64_t)p;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)1U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterbound;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t bound;
  size_t p2;
  uint64_t fieldStartS;
  size_t p3;
  uint64_t fieldStarttpointer;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAftertpointer;
  uint8_t resultAfterS;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  uint8_t first;
  size_t pos_;
  uint8_t first1;
  size_t pos_1;
  uint8_t first2;
  size_t pos_2;
  uint8_t first3;
  size_t pos_3;
  uint8_t first4;
  size_t pos_4;
  uint8_t first5;
  size_t pos_5;
  uint8_t first6;
  uint8_t first7;
  uint64_t n;
  uint64_t bfirst;
  uint64_t n1;
  uint64_t bfirst1;
  uint64_t n2;
  uint64_t bfirst2;
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t tpointer;
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
  BOOLEAN actionSuccessTpointer;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res1;
  if (hasBytes)
  {
    pos = p0 + (size_t)1U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterbound = res;
  }
  else
  {
    ErrorHandlerFn("_S",
      "bound",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterbound = res;
  }
  if (resultAfterbound == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)1U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    bound = sub[0U];
    p2 = SlPos[0U];
    fieldStartS = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStarttpointer = (uint64_t)p3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p02 = pos1;
    p4 = SlPos[0U];
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)8U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)8U;
      resultAftertpointer = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftertpointer = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftertpointer == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p03 = SlPos[0U];
      m1 = p03 + (size_t)8U;
      sub1 = SlBase + p03;
      SlPos[0U] = m1;
      first = sub1[0U];
      pos_ = (size_t)2U;
      first1 = sub1[1U];
      pos_1 = pos_ + (size_t)1U;
      first2 = sub1[pos_];
      pos_2 = pos_1 + (size_t)1U;
      first3 = sub1[pos_1];
      pos_3 = pos_2 + (size_t)1U;
      first4 = sub1[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first5 = sub1[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first6 = sub1[pos_4];
      first7 = sub1[pos_5];
      n = (uint64_t)(uint32_t)first7;
      bfirst = (uint64_t)(uint32_t)first6;
      n1 = bfirst + n * 256ULL;
      bfirst1 = (uint64_t)(uint32_t)first5;
      n2 = bfirst1 + n1 * 256ULL;
      bfirst2 = (uint64_t)(uint32_t)first4;
      n3 = bfirst2 + n2 * 256ULL;
      bfirst3 = (uint64_t)(uint32_t)first3;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first2;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first1;
      n6 = bfirst5 + n5 * 256ULL;
      bfirst6 = (uint64_t)(uint32_t)first;
      tpointer = bfirst6 + n6 * 256ULL;
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit2("_S.tpointer", (uint64_t)4U, Dest);
      if (ok)
      {
        rd = readOffset;
        wr0 = writeOffset;
        ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr0, tpointer, Dest);
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
        base = EverParseStreamOf(Dest);
        len = (size_t)EverParseStreamLen(Dest);
        cursor = (size_t)0U;
        res1 = ProbeValidateCoreT((uint32_t)bound, Ctxt, ErrorHandlerFn, base, len, &cursor);
        actionSuccessTpointer = res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("_S",
          "tpointer",
          EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
            (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                         : 15ULL,
          Ctxt,
          SlBase,
          fieldStarttpointer);
        actionSuccessTpointer = FALSE;
      }
      resultAfterS =
        actionSuccessTpointer ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                              : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterS = resultAftertpointer;
    }
    if (resultAfterS == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterS;
    }
    ErrorHandlerFn("_S",
      "tpointer",
      EverParsePulseInternalErrorReasonOfResult(resultAfterS),
      resultAfterS == 0U || (resultAfterS >= 2U && resultAfterS <= 8U) ? (uint64_t)(uint32_t)resultAfterS
                                                                       : 15ULL,
      Ctxt,
      SlBase,
      fieldStartS);
    return resultAfterS;
  }
  return resultAfterbound;
}

uint64_t
ProbeValidateS(
  EVERPARSE_COPY_BUFFER_T Dest,
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
  uint8_t status = ProbeValidateCoreS(Dest, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreU(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  size_t pos = (size_t)0U;
  /* Validating field tag */
  size_t p = SlPos[0U];
  uint64_t viewStart = (uint64_t)p;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)1U <= (rem - p0);
  uint8_t res;
  uint8_t res1;
  uint8_t resultAftertag;
  size_t consumed;
  size_t p20;
  size_t p_;
  size_t p2;
  uint64_t fieldStartU;
  size_t p3;
  uint64_t fieldStartspointer;
  size_t pos1;
  size_t p01;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterspointer;
  uint8_t resultAfterU;
  size_t p02;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  size_t pos_;
  uint8_t first1;
  size_t pos_1;
  uint8_t first2;
  size_t pos_2;
  uint8_t first3;
  size_t pos_3;
  uint8_t first4;
  size_t pos_4;
  uint8_t first5;
  size_t pos_5;
  uint8_t first6;
  uint8_t first7;
  uint64_t n;
  uint64_t bfirst;
  uint64_t n1;
  uint64_t bfirst1;
  uint64_t n2;
  uint64_t bfirst2;
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t spointer;
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
  BOOLEAN actionSuccessSpointer;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res2;
  if (hasBytes)
  {
    pos = p0 + (size_t)1U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res1 = res;
  }
  else
  {
    ErrorHandlerFn("_U",
      "tag",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    res1 = res;
  }
  if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p20 = SlPos[0U];
    p_ = p20 + consumed;
    SlPos[0U] = p_;
    resultAftertag = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftertag = res1;
  }
  if (resultAftertag == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p2 = SlPos[0U];
    fieldStartU = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStartspointer = (uint64_t)p3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p01 = pos1;
    p4 = SlPos[0U];
    rem1 = SlLen - p4;
    hasBytes1 = p01 <= rem1 && (size_t)8U <= (rem1 - p01);
    if (hasBytes1)
    {
      pos1 = p01 + (size_t)8U;
      resultAfterspointer = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterspointer = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterspointer == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p02 = SlPos[0U];
      m = p02 + (size_t)8U;
      sub = SlBase + p02;
      SlPos[0U] = m;
      first = sub[0U];
      pos_ = (size_t)2U;
      first1 = sub[1U];
      pos_1 = pos_ + (size_t)1U;
      first2 = sub[pos_];
      pos_2 = pos_1 + (size_t)1U;
      first3 = sub[pos_1];
      pos_3 = pos_2 + (size_t)1U;
      first4 = sub[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first5 = sub[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first6 = sub[pos_4];
      first7 = sub[pos_5];
      n = (uint64_t)(uint32_t)first7;
      bfirst = (uint64_t)(uint32_t)first6;
      n1 = bfirst + n * 256ULL;
      bfirst1 = (uint64_t)(uint32_t)first5;
      n2 = bfirst1 + n1 * 256ULL;
      bfirst2 = (uint64_t)(uint32_t)first4;
      n3 = bfirst2 + n2 * 256ULL;
      bfirst3 = (uint64_t)(uint32_t)first3;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first2;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first1;
      n6 = bfirst5 + n5 * 256ULL;
      bfirst6 = (uint64_t)(uint32_t)first;
      spointer = bfirst6 + n6 * 256ULL;
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed = FALSE;
      ok = ProbeInit2("_U.spointer", (uint64_t)9U, DestS);
      if (ok)
      {
        rd = readOffset;
        wr0 = writeOffset;
        ok1 = ProbeAndCopy2((uint64_t)9U, rd, wr0, spointer, DestS);
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
        base = EverParseStreamOf(DestS);
        len = (size_t)EverParseStreamLen(DestS);
        cursor = (size_t)0U;
        res2 = ProbeValidateCoreS(DestT, Ctxt, ErrorHandlerFn, base, len, &cursor);
        actionSuccessSpointer = res2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("_U",
          "spointer",
          EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
            (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                         : 15ULL,
          Ctxt,
          SlBase,
          fieldStartspointer);
        actionSuccessSpointer = FALSE;
      }
      resultAfterU =
        actionSuccessSpointer ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                              : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterU = resultAfterspointer;
    }
    if (resultAfterU == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterU;
    }
    ErrorHandlerFn("_U",
      "spointer",
      EverParsePulseInternalErrorReasonOfResult(resultAfterU),
      resultAfterU == 0U || (resultAfterU >= 2U && resultAfterU <= 8U) ? (uint64_t)(uint32_t)resultAfterU
                                                                       : 15ULL,
      Ctxt,
      SlBase,
      fieldStartU);
    return resultAfterU;
  }
  return resultAftertag;
}

uint64_t
ProbeValidateU(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  uint8_t status = ProbeValidateCoreU(DestS, DestT, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreV(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  size_t pos = (size_t)0U;
  size_t p = SlPos[0U];
  uint64_t viewStart = (uint64_t)p;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)1U <= (rem - p0);
  uint8_t res;
  uint8_t resultAftertag;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t tag;
  size_t p2;
  uint64_t fieldStartV;
  size_t p3;
  uint64_t fieldStartsptr;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAftersptr;
  uint8_t resultAfterV;
  size_t p030;
  size_t m10;
  uint8_t *sub10;
  uint8_t first0;
  size_t pos_;
  uint8_t first10;
  size_t pos_1;
  uint8_t first20;
  size_t pos_2;
  uint8_t first30;
  size_t pos_3;
  uint8_t first40;
  size_t pos_4;
  uint8_t first50;
  size_t pos_5;
  uint8_t first60;
  uint8_t first70;
  uint64_t n0;
  uint64_t bfirst0;
  uint64_t n10;
  uint64_t bfirst10;
  uint64_t n20;
  uint64_t bfirst20;
  uint64_t n30;
  uint64_t bfirst30;
  uint64_t n40;
  uint64_t bfirst40;
  uint64_t n50;
  uint64_t bfirst50;
  uint64_t n60;
  uint64_t bfirst60;
  uint64_t sptr;
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
  BOOLEAN actionSuccessSptr;
  uint8_t *base0;
  size_t len0;
  size_t cursor0;
  uint8_t res10;
  uint8_t resultAftersptr1;
  size_t p5;
  uint64_t fieldStartV1;
  size_t p6;
  uint64_t fieldStarttptr;
  size_t pos2;
  size_t p03;
  size_t p7;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t resultAftertptr;
  uint8_t resultAfterV1;
  size_t p040;
  size_t m11;
  uint8_t *sub11;
  uint8_t first8;
  size_t pos_0;
  uint8_t first11;
  size_t pos_10;
  uint8_t first21;
  size_t pos_20;
  uint8_t first31;
  size_t pos_30;
  uint8_t first41;
  size_t pos_40;
  uint8_t first51;
  size_t pos_50;
  uint8_t first61;
  uint8_t first71;
  uint64_t n7;
  uint64_t bfirst7;
  uint64_t n11;
  uint64_t bfirst11;
  uint64_t n21;
  uint64_t bfirst21;
  uint64_t n31;
  uint64_t bfirst31;
  uint64_t n41;
  uint64_t bfirst41;
  uint64_t n51;
  uint64_t bfirst51;
  uint64_t n61;
  uint64_t bfirst61;
  uint64_t tptr;
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
  BOOLEAN actionSuccessTptr;
  uint8_t *base1;
  size_t len1;
  size_t cursor1;
  uint8_t res11;
  uint8_t resultAftertptr1;
  size_t p8;
  uint64_t fieldStartV2;
  size_t p9;
  uint64_t fieldStartt2ptr;
  size_t pos3;
  size_t p04;
  size_t p10;
  size_t rem3;
  BOOLEAN hasBytes3;
  uint8_t resultAftert2ptr;
  uint8_t resultAfterV2;
  size_t p05;
  size_t m1;
  uint8_t *sub1;
  uint8_t first;
  size_t pos_6;
  uint8_t first1;
  size_t pos_11;
  uint8_t first2;
  size_t pos_21;
  uint8_t first3;
  size_t pos_31;
  uint8_t first4;
  size_t pos_41;
  uint8_t first5;
  size_t pos_51;
  uint8_t first6;
  uint8_t first7;
  uint64_t n;
  uint64_t bfirst;
  uint64_t n1;
  uint64_t bfirst1;
  uint64_t n2;
  uint64_t bfirst2;
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t t2ptr;
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
  BOOLEAN actionSuccessT2ptr;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res1;
  if (hasBytes)
  {
    pos = p0 + (size_t)1U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAftertag = res;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tag",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAftertag = res;
  }
  if (resultAftertag == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)1U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    tag = sub[0U];
    p2 = SlPos[0U];
    fieldStartV = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStartsptr = (uint64_t)p3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p02 = pos1;
    p4 = SlPos[0U];
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)8U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)8U;
      resultAftersptr = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftersptr = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftersptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p030 = SlPos[0U];
      m10 = p030 + (size_t)8U;
      sub10 = SlBase + p030;
      SlPos[0U] = m10;
      first0 = sub10[0U];
      pos_ = (size_t)2U;
      first10 = sub10[1U];
      pos_1 = pos_ + (size_t)1U;
      first20 = sub10[pos_];
      pos_2 = pos_1 + (size_t)1U;
      first30 = sub10[pos_1];
      pos_3 = pos_2 + (size_t)1U;
      first40 = sub10[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first50 = sub10[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first60 = sub10[pos_4];
      first70 = sub10[pos_5];
      n0 = (uint64_t)(uint32_t)first70;
      bfirst0 = (uint64_t)(uint32_t)first60;
      n10 = bfirst0 + n0 * 256ULL;
      bfirst10 = (uint64_t)(uint32_t)first50;
      n20 = bfirst10 + n10 * 256ULL;
      bfirst20 = (uint64_t)(uint32_t)first40;
      n30 = bfirst20 + n20 * 256ULL;
      bfirst30 = (uint64_t)(uint32_t)first30;
      n40 = bfirst30 + n30 * 256ULL;
      bfirst40 = (uint64_t)(uint32_t)first20;
      n50 = bfirst40 + n40 * 256ULL;
      bfirst50 = (uint64_t)(uint32_t)first10;
      n60 = bfirst50 + n50 * 256ULL;
      bfirst60 = (uint64_t)(uint32_t)first0;
      sptr = bfirst60 + n60 * 256ULL;
      readOffset = 0ULL;
      writeOffset = 0ULL;
      failed0 = FALSE;
      ok0 = ProbeInit2("_V.sptr", (uint64_t)9U, DestS);
      if (ok0)
      {
        rd0 = readOffset;
        wr0 = writeOffset;
        ok10 = ProbeAndCopy2((uint64_t)9U, rd0, wr0, sptr, DestS);
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
        base0 = EverParseStreamOf(DestS);
        len0 = (size_t)EverParseStreamLen(DestS);
        cursor0 = (size_t)0U;
        res10 = ProbeValidateCoreS(DestT, Ctxt, ErrorHandlerFn, base0, len0, &cursor0);
        actionSuccessSptr = res10 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("_V",
          "sptr",
          EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
            (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                         : 15ULL,
          Ctxt,
          SlBase,
          fieldStartsptr);
        actionSuccessSptr = FALSE;
      }
      resultAfterV =
        actionSuccessSptr ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                          : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterV = resultAftersptr;
    }
    if (resultAfterV == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      resultAftersptr1 = resultAfterV;
    }
    else
    {
      ErrorHandlerFn("_V",
        "sptr",
        EverParsePulseInternalErrorReasonOfResult(resultAfterV),
        resultAfterV == 0U || (resultAfterV >= 2U && resultAfterV <= 8U) ? (uint64_t)(uint32_t)resultAfterV
                                                                         : 15ULL,
        Ctxt,
        SlBase,
        fieldStartV);
      resultAftersptr1 = resultAfterV;
    }
    if (resultAftersptr1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p5 = SlPos[0U];
      fieldStartV1 = (uint64_t)p5;
      p6 = SlPos[0U];
      fieldStarttptr = (uint64_t)p6;
      pos2 = (size_t)0U;
      /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
      p03 = pos2;
      p7 = SlPos[0U];
      rem2 = SlLen - p7;
      hasBytes2 = p03 <= rem2 && (size_t)8U <= (rem2 - p03);
      if (hasBytes2)
      {
        pos2 = p03 + (size_t)8U;
        resultAftertptr = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAftertptr = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (resultAftertptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        p040 = SlPos[0U];
        m11 = p040 + (size_t)8U;
        sub11 = SlBase + p040;
        SlPos[0U] = m11;
        first8 = sub11[0U];
        pos_0 = (size_t)2U;
        first11 = sub11[1U];
        pos_10 = pos_0 + (size_t)1U;
        first21 = sub11[pos_0];
        pos_20 = pos_10 + (size_t)1U;
        first31 = sub11[pos_10];
        pos_30 = pos_20 + (size_t)1U;
        first41 = sub11[pos_20];
        pos_40 = pos_30 + (size_t)1U;
        first51 = sub11[pos_30];
        pos_50 = pos_40 + (size_t)1U;
        first61 = sub11[pos_40];
        first71 = sub11[pos_50];
        n7 = (uint64_t)(uint32_t)first71;
        bfirst7 = (uint64_t)(uint32_t)first61;
        n11 = bfirst7 + n7 * 256ULL;
        bfirst11 = (uint64_t)(uint32_t)first51;
        n21 = bfirst11 + n11 * 256ULL;
        bfirst21 = (uint64_t)(uint32_t)first41;
        n31 = bfirst21 + n21 * 256ULL;
        bfirst31 = (uint64_t)(uint32_t)first31;
        n41 = bfirst31 + n31 * 256ULL;
        bfirst41 = (uint64_t)(uint32_t)first21;
        n51 = bfirst41 + n41 * 256ULL;
        bfirst51 = (uint64_t)(uint32_t)first11;
        n61 = bfirst51 + n51 * 256ULL;
        bfirst61 = (uint64_t)(uint32_t)first8;
        tptr = bfirst61 + n61 * 256ULL;
        readOffset0 = 0ULL;
        writeOffset0 = 0ULL;
        failed1 = FALSE;
        ok2 = ProbeInit2("_V.tptr", (uint64_t)8U, DestT);
        if (ok2)
        {
          rd1 = readOffset0;
          wr2 = writeOffset0;
          ok11 = ProbeAndCopy2((uint64_t)8U, rd1, wr2, tptr, DestT);
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
          base1 = EverParseStreamOf(DestT);
          len1 = (size_t)EverParseStreamLen(DestT);
          cursor1 = (size_t)0U;
          res11 = ProbeValidateCoreT((uint32_t)17U, Ctxt, ErrorHandlerFn, base1, len1, &cursor1);
          actionSuccessTptr = res11 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          ErrorHandlerFn("_V",
            "tptr",
            EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
            EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
              (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
                EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                           : 15ULL,
            Ctxt,
            SlBase,
            fieldStarttptr);
          actionSuccessTptr = FALSE;
        }
        resultAfterV1 =
          actionSuccessTptr ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                            : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
      }
      else
      {
        resultAfterV1 = resultAftertptr;
      }
      if (resultAfterV1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        resultAftertptr1 = resultAfterV1;
      }
      else
      {
        ErrorHandlerFn("_V",
          "tptr",
          EverParsePulseInternalErrorReasonOfResult(resultAfterV1),
          resultAfterV1 == 0U || (resultAfterV1 >= 2U && resultAfterV1 <= 8U) ? (uint64_t)(uint32_t)resultAfterV1
                                                                              : 15ULL,
          Ctxt,
          SlBase,
          fieldStartV1);
        resultAftertptr1 = resultAfterV1;
      }
      if (resultAftertptr1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        p8 = SlPos[0U];
        fieldStartV2 = (uint64_t)p8;
        p9 = SlPos[0U];
        fieldStartt2ptr = (uint64_t)p9;
        pos3 = (size_t)0U;
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        p04 = pos3;
        p10 = SlPos[0U];
        rem3 = SlLen - p10;
        hasBytes3 = p04 <= rem3 && (size_t)8U <= (rem3 - p04);
        if (hasBytes3)
        {
          pos3 = p04 + (size_t)8U;
          resultAftert2ptr = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAftert2ptr = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (resultAftert2ptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          p05 = SlPos[0U];
          m1 = p05 + (size_t)8U;
          sub1 = SlBase + p05;
          SlPos[0U] = m1;
          first = sub1[0U];
          pos_6 = (size_t)2U;
          first1 = sub1[1U];
          pos_11 = pos_6 + (size_t)1U;
          first2 = sub1[pos_6];
          pos_21 = pos_11 + (size_t)1U;
          first3 = sub1[pos_11];
          pos_31 = pos_21 + (size_t)1U;
          first4 = sub1[pos_21];
          pos_41 = pos_31 + (size_t)1U;
          first5 = sub1[pos_31];
          pos_51 = pos_41 + (size_t)1U;
          first6 = sub1[pos_41];
          first7 = sub1[pos_51];
          n = (uint64_t)(uint32_t)first7;
          bfirst = (uint64_t)(uint32_t)first6;
          n1 = bfirst + n * 256ULL;
          bfirst1 = (uint64_t)(uint32_t)first5;
          n2 = bfirst1 + n1 * 256ULL;
          bfirst2 = (uint64_t)(uint32_t)first4;
          n3 = bfirst2 + n2 * 256ULL;
          bfirst3 = (uint64_t)(uint32_t)first3;
          n4 = bfirst3 + n3 * 256ULL;
          bfirst4 = (uint64_t)(uint32_t)first2;
          n5 = bfirst4 + n4 * 256ULL;
          bfirst5 = (uint64_t)(uint32_t)first1;
          n6 = bfirst5 + n5 * 256ULL;
          bfirst6 = (uint64_t)(uint32_t)first;
          t2ptr = bfirst6 + n6 * 256ULL;
          readOffset1 = 0ULL;
          writeOffset1 = 0ULL;
          failed = FALSE;
          ok = ProbeInit2("_V.t2ptr", (uint64_t)8U, DestT);
          if (ok)
          {
            rd = readOffset1;
            wr4 = writeOffset1;
            ok1 = ProbeAndCopy2((uint64_t)8U, rd, wr4, t2ptr, DestT);
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
            base = EverParseStreamOf(DestT);
            len = (size_t)EverParseStreamLen(DestT);
            cursor = (size_t)0U;
            res1 = ProbeValidateCoreT((uint32_t)tag, Ctxt, ErrorHandlerFn, base, len, &cursor);
            actionSuccessT2ptr = res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          }
          else
          {
            ErrorHandlerFn("_V",
              "t2ptr",
              EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
                (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
                  EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                             : 15ULL,
              Ctxt,
              SlBase,
              fieldStartt2ptr);
            actionSuccessT2ptr = FALSE;
          }
          resultAfterV2 =
            actionSuccessT2ptr ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                               : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
        }
        else
        {
          resultAfterV2 = resultAftert2ptr;
        }
        if (resultAfterV2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          return resultAfterV2;
        }
        ErrorHandlerFn("_V",
          "t2ptr",
          EverParsePulseInternalErrorReasonOfResult(resultAfterV2),
          resultAfterV2 == 0U || (resultAfterV2 >= 2U && resultAfterV2 <= 8U) ? (uint64_t)(uint32_t)resultAfterV2
                                                                              : 15ULL,
          Ctxt,
          SlBase,
          fieldStartV2);
        return resultAfterV2;
      }
      return resultAftertptr1;
    }
    return resultAftersptr1;
  }
  return resultAftertag;
}

uint64_t
ProbeValidateV(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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
  uint8_t status = ProbeValidateCoreV(DestS, DestT, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreIndirect(
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
  size_t p = SlPos[0U];
  uint64_t fieldStartIndirect = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)9U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterIndirect;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)9U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterIndirect = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterIndirect = res;
  }
  if (resultAfterIndirect == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterIndirect;
  }
  ErrorHandlerFn("_Indirect",
    "fst",
    EverParsePulseInternalErrorReasonOfResult(resultAfterIndirect),
    resultAfterIndirect == 0U || (resultAfterIndirect >= 2U && resultAfterIndirect <= 8U) ? (uint64_t)(uint32_t)resultAfterIndirect
                                                                                          : 15ULL,
    Ctxt,
    SlBase,
    fieldStartIndirect);
  return resultAfterIndirect;
}

uint64_t
ProbeValidateIndirect(
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
  uint8_t status = ProbeValidateCoreIndirect(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

inline uint8_t
ProbeValidateCoreTt(
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
  size_t p = SlPos[0U];
  uint64_t fieldStartTt = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)9U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterTt;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)9U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterTt = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterTt = res;
  }
  if (resultAfterTt == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterTt;
  }
  ErrorHandlerFn("_TT",
    "fst",
    EverParsePulseInternalErrorReasonOfResult(resultAfterTt),
    resultAfterTt == 0U || (resultAfterTt >= 2U && resultAfterTt <= 8U) ? (uint64_t)(uint32_t)resultAfterTt
                                                                        : 15ULL,
    Ctxt,
    SlBase,
    fieldStartTt);
  return resultAfterTt;
}

uint8_t
ProbeValidateCoreI(
  EVERPARSE_COPY_BUFFER_T Dest,
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
  size_t p = SlPos[0U];
  uint64_t fieldStartI = (uint64_t)p;
  size_t p1 = SlPos[0U];
  uint64_t fieldStartttptr = (uint64_t)p1;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  size_t p0 = pos;
  size_t p2 = SlPos[0U];
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t resultAfterttptr;
  uint8_t resultAfterI;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  size_t pos_;
  uint8_t first1;
  size_t pos_1;
  uint8_t first2;
  size_t pos_2;
  uint8_t first3;
  size_t pos_3;
  uint8_t first4;
  size_t pos_4;
  uint8_t first5;
  size_t pos_5;
  uint8_t first6;
  uint8_t first7;
  uint64_t n;
  uint64_t bfirst;
  uint64_t n1;
  uint64_t bfirst1;
  uint64_t n2;
  uint64_t bfirst2;
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t ttptr;
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
  BOOLEAN actionSuccessTtptr;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (hasBytes)
  {
    pos = p0 + (size_t)8U;
    resultAfterttptr = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterttptr = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterttptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)8U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    first = sub[0U];
    pos_ = (size_t)2U;
    first1 = sub[1U];
    pos_1 = pos_ + (size_t)1U;
    first2 = sub[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first3 = sub[pos_1];
    pos_3 = pos_2 + (size_t)1U;
    first4 = sub[pos_2];
    pos_4 = pos_3 + (size_t)1U;
    first5 = sub[pos_3];
    pos_5 = pos_4 + (size_t)1U;
    first6 = sub[pos_4];
    first7 = sub[pos_5];
    n = (uint64_t)(uint32_t)first7;
    bfirst = (uint64_t)(uint32_t)first6;
    n1 = bfirst + n * 256ULL;
    bfirst1 = (uint64_t)(uint32_t)first5;
    n2 = bfirst1 + n1 * 256ULL;
    bfirst2 = (uint64_t)(uint32_t)first4;
    n3 = bfirst2 + n2 * 256ULL;
    bfirst3 = (uint64_t)(uint32_t)first3;
    n4 = bfirst3 + n3 * 256ULL;
    bfirst4 = (uint64_t)(uint32_t)first2;
    n5 = bfirst4 + n4 * 256ULL;
    bfirst5 = (uint64_t)(uint32_t)first1;
    n6 = bfirst5 + n5 * 256ULL;
    bfirst6 = (uint64_t)(uint32_t)first;
    ttptr = bfirst6 + n6 * 256ULL;
    readOffset = 0ULL;
    writeOffset = 0ULL;
    failed = FALSE;
    ok = ProbeInit2("_I.ttptr", (uint64_t)9U, Dest);
    if (ok)
    {
      rd = readOffset;
      wr0 = writeOffset;
      ok1 = ProbeAndCopy2((uint64_t)9U, rd, wr0, ttptr, Dest);
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
      base = EverParseStreamOf(Dest);
      len = (size_t)EverParseStreamLen(Dest);
      cursor = (size_t)0U;
      res = ProbeValidateCoreTt(Ctxt, ErrorHandlerFn, base, len, &cursor);
      actionSuccessTtptr = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      ErrorHandlerFn("_I",
        "ttptr",
        EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
        EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
          (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
            EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                       : 15ULL,
        Ctxt,
        SlBase,
        fieldStartttptr);
      actionSuccessTtptr = FALSE;
    }
    resultAfterI =
      actionSuccessTtptr ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                         : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
  }
  else
  {
    resultAfterI = resultAfterttptr;
  }
  if (resultAfterI == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterI;
  }
  ErrorHandlerFn("_I",
    "ttptr",
    EverParsePulseInternalErrorReasonOfResult(resultAfterI),
    resultAfterI == 0U || (resultAfterI >= 2U && resultAfterI <= 8U) ? (uint64_t)(uint32_t)resultAfterI
                                                                     : 15ULL,
    Ctxt,
    SlBase,
    fieldStartI);
  return resultAfterI;
}

uint64_t
ProbeValidateI(
  EVERPARSE_COPY_BUFFER_T Dest,
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
  uint8_t status = ProbeValidateCoreI(Dest, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreMultiProbe(
  EVERPARSE_COPY_BUFFER_T DestT1,
  EVERPARSE_COPY_BUFFER_T DestT2,
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
  size_t pos = (size_t)0U;
  /* Validating field fst */
  size_t p = SlPos[0U];
  uint64_t viewStart = (uint64_t)p;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t res;
  uint8_t res1;
  uint8_t resultAfterfst;
  size_t consumed0;
  size_t p20;
  size_t p_;
  size_t pos1;
  size_t p2;
  uint64_t viewStart1;
  size_t fieldOff1;
  uint64_t startPos1;
  size_t p01;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res2;
  uint8_t res3;
  uint8_t resultAftersnd;
  size_t consumed1;
  size_t p40;
  size_t p_0;
  size_t pos2;
  size_t p4;
  uint64_t viewStart2;
  size_t fieldOff2;
  uint64_t startPos2;
  size_t p02;
  size_t p5;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t res4;
  uint8_t res5;
  uint8_t resultAftertag;
  size_t consumed;
  size_t p60;
  size_t p_1;
  size_t p6;
  uint64_t fieldStartMultiProbe;
  size_t p7;
  uint64_t fieldStarttptr1;
  size_t pos3;
  size_t p03;
  size_t p8;
  size_t rem3;
  BOOLEAN hasBytes3;
  uint8_t resultAftertptr1;
  uint8_t resultAfterMultiProbe;
  size_t p040;
  size_t m0;
  uint8_t *sub0;
  uint8_t first0;
  size_t pos_;
  uint8_t first10;
  size_t pos_1;
  uint8_t first20;
  size_t pos_2;
  uint8_t first30;
  size_t pos_3;
  uint8_t first40;
  size_t pos_4;
  uint8_t first50;
  size_t pos_5;
  uint8_t first60;
  uint8_t first70;
  uint64_t n0;
  uint64_t bfirst0;
  uint64_t n10;
  uint64_t bfirst10;
  uint64_t n20;
  uint64_t bfirst20;
  uint64_t n30;
  uint64_t bfirst30;
  uint64_t n40;
  uint64_t bfirst40;
  uint64_t n50;
  uint64_t bfirst50;
  uint64_t n60;
  uint64_t bfirst60;
  uint64_t tptr1;
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
  BOOLEAN actionSuccessTptr1;
  uint8_t *base0;
  size_t len0;
  size_t cursor0;
  uint8_t res60;
  uint8_t resultAftertptr11;
  size_t p9;
  uint64_t fieldStartMultiProbe1;
  size_t p10;
  uint64_t fieldStarttptr2;
  size_t pos4;
  size_t p04;
  size_t p11;
  size_t rem4;
  BOOLEAN hasBytes4;
  uint8_t resultAftertptr2;
  uint8_t resultAfterMultiProbe1;
  size_t p05;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  size_t pos_0;
  uint8_t first1;
  size_t pos_10;
  uint8_t first2;
  size_t pos_20;
  uint8_t first3;
  size_t pos_30;
  uint8_t first4;
  size_t pos_40;
  uint8_t first5;
  size_t pos_50;
  uint8_t first6;
  uint8_t first7;
  uint64_t n;
  uint64_t bfirst;
  uint64_t n1;
  uint64_t bfirst1;
  uint64_t n2;
  uint64_t bfirst2;
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t tptr2;
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
  BOOLEAN actionSuccessTptr2;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res6;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res1 = res;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "fst",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    res1 = res;
  }
  if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed0 = pos;
    p20 = SlPos[0U];
    p_ = p20 + consumed0;
    SlPos[0U] = p_;
    resultAfterfst = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterfst = res1;
  }
  if (resultAfterfst == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    pos1 = (size_t)0U;
    /* Validating field snd */
    p2 = SlPos[0U];
    viewStart1 = (uint64_t)p2;
    fieldOff1 = pos1;
    startPos1 = viewStart1 + (uint64_t)fieldOff1;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p01 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p01 <= rem1 && (size_t)4U <= (rem1 - p01);
    if (hasBytes1)
    {
      pos1 = p01 + (size_t)4U;
      res2 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res2 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      res3 = res2;
    }
    else
    {
      ErrorHandlerFn("_MultiProbe",
        "snd",
        EverParsePulseInternalErrorReasonOfResult(res2),
        res2 == 0U || (res2 >= 2U && res2 <= 8U) ? (uint64_t)(uint32_t)res2 : 15ULL,
        Ctxt,
        SlBase,
        startPos1);
      res3 = res2;
    }
    if (res3 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed1 = pos1;
      p40 = SlPos[0U];
      p_0 = p40 + consumed1;
      SlPos[0U] = p_0;
      resultAftersnd = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftersnd = res3;
    }
    if (resultAftersnd == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      pos2 = (size_t)0U;
      /* Validating field tag */
      p4 = SlPos[0U];
      viewStart2 = (uint64_t)p4;
      fieldOff2 = pos2;
      startPos2 = viewStart2 + (uint64_t)fieldOff2;
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      p02 = pos2;
      p5 = SlPos[0U];
      rem2 = SlLen - p5;
      hasBytes2 = p02 <= rem2 && (size_t)1U <= (rem2 - p02);
      if (hasBytes2)
      {
        pos2 = p02 + (size_t)1U;
        res4 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        res4 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (res4 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        res5 = res4;
      }
      else
      {
        ErrorHandlerFn("_MultiProbe",
          "tag",
          EverParsePulseInternalErrorReasonOfResult(res4),
          res4 == 0U || (res4 >= 2U && res4 <= 8U) ? (uint64_t)(uint32_t)res4 : 15ULL,
          Ctxt,
          SlBase,
          startPos2);
        res5 = res4;
      }
      if (res5 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        consumed = pos2;
        p60 = SlPos[0U];
        p_1 = p60 + consumed;
        SlPos[0U] = p_1;
        resultAftertag = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAftertag = res5;
      }
      if (resultAftertag == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        p6 = SlPos[0U];
        fieldStartMultiProbe = (uint64_t)p6;
        p7 = SlPos[0U];
        fieldStarttptr1 = (uint64_t)p7;
        pos3 = (size_t)0U;
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        p03 = pos3;
        p8 = SlPos[0U];
        rem3 = SlLen - p8;
        hasBytes3 = p03 <= rem3 && (size_t)8U <= (rem3 - p03);
        if (hasBytes3)
        {
          pos3 = p03 + (size_t)8U;
          resultAftertptr1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAftertptr1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (resultAftertptr1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          p040 = SlPos[0U];
          m0 = p040 + (size_t)8U;
          sub0 = SlBase + p040;
          SlPos[0U] = m0;
          first0 = sub0[0U];
          pos_ = (size_t)2U;
          first10 = sub0[1U];
          pos_1 = pos_ + (size_t)1U;
          first20 = sub0[pos_];
          pos_2 = pos_1 + (size_t)1U;
          first30 = sub0[pos_1];
          pos_3 = pos_2 + (size_t)1U;
          first40 = sub0[pos_2];
          pos_4 = pos_3 + (size_t)1U;
          first50 = sub0[pos_3];
          pos_5 = pos_4 + (size_t)1U;
          first60 = sub0[pos_4];
          first70 = sub0[pos_5];
          n0 = (uint64_t)(uint32_t)first70;
          bfirst0 = (uint64_t)(uint32_t)first60;
          n10 = bfirst0 + n0 * 256ULL;
          bfirst10 = (uint64_t)(uint32_t)first50;
          n20 = bfirst10 + n10 * 256ULL;
          bfirst20 = (uint64_t)(uint32_t)first40;
          n30 = bfirst20 + n20 * 256ULL;
          bfirst30 = (uint64_t)(uint32_t)first30;
          n40 = bfirst30 + n30 * 256ULL;
          bfirst40 = (uint64_t)(uint32_t)first20;
          n50 = bfirst40 + n40 * 256ULL;
          bfirst50 = (uint64_t)(uint32_t)first10;
          n60 = bfirst50 + n50 * 256ULL;
          bfirst60 = (uint64_t)(uint32_t)first0;
          tptr1 = bfirst60 + n60 * 256ULL;
          readOffset = 0ULL;
          writeOffset = 0ULL;
          failed0 = FALSE;
          ok0 = ProbeInit2("_MultiProbe.tptr1", (uint64_t)4U, DestT1);
          if (ok0)
          {
            rd0 = readOffset;
            wr0 = writeOffset;
            ok10 = ProbeAndCopy2((uint64_t)4U, rd0, wr0, tptr1, DestT1);
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
            ErrorHandlerFn("_MultiProbe",
              "tptr1",
              "probe",
              0ULL,
              Ctxt,
              EverParseStreamOf(DestT1),
              0ULL);
            b0 = 0ULL;
          }
          else
          {
            b0 = wr1;
          }
          if (b0 != 0ULL)
          {
            base0 = EverParseStreamOf(DestT1);
            len0 = (size_t)EverParseStreamLen(DestT1);
            cursor0 = (size_t)0U;
            res60 = ProbeValidateCoreT((uint32_t)17U, Ctxt, ErrorHandlerFn, base0, len0, &cursor0);
            actionSuccessTptr1 = res60 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          }
          else
          {
            ErrorHandlerFn("_MultiProbe",
              "tptr1",
              EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
                (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
                  EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                             : 15ULL,
              Ctxt,
              SlBase,
              fieldStarttptr1);
            actionSuccessTptr1 = FALSE;
          }
          resultAfterMultiProbe =
            actionSuccessTptr1 ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                               : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
        }
        else
        {
          resultAfterMultiProbe = resultAftertptr1;
        }
        if (resultAfterMultiProbe == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          resultAftertptr11 = resultAfterMultiProbe;
        }
        else
        {
          ErrorHandlerFn("_MultiProbe",
            "tptr1",
            EverParsePulseInternalErrorReasonOfResult(resultAfterMultiProbe),
            resultAfterMultiProbe == 0U ||
              (resultAfterMultiProbe >= 2U && resultAfterMultiProbe <= 8U) ? (uint64_t)(uint32_t)resultAfterMultiProbe
                                                                           : 15ULL,
            Ctxt,
            SlBase,
            fieldStartMultiProbe);
          resultAftertptr11 = resultAfterMultiProbe;
        }
        if (resultAftertptr11 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          p9 = SlPos[0U];
          fieldStartMultiProbe1 = (uint64_t)p9;
          p10 = SlPos[0U];
          fieldStarttptr2 = (uint64_t)p10;
          pos4 = (size_t)0U;
          /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
          p04 = pos4;
          p11 = SlPos[0U];
          rem4 = SlLen - p11;
          hasBytes4 = p04 <= rem4 && (size_t)8U <= (rem4 - p04);
          if (hasBytes4)
          {
            pos4 = p04 + (size_t)8U;
            resultAftertptr2 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          }
          else
          {
            resultAftertptr2 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
          }
          if (resultAftertptr2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
          {
            p05 = SlPos[0U];
            m = p05 + (size_t)8U;
            sub = SlBase + p05;
            SlPos[0U] = m;
            first = sub[0U];
            pos_0 = (size_t)2U;
            first1 = sub[1U];
            pos_10 = pos_0 + (size_t)1U;
            first2 = sub[pos_0];
            pos_20 = pos_10 + (size_t)1U;
            first3 = sub[pos_10];
            pos_30 = pos_20 + (size_t)1U;
            first4 = sub[pos_20];
            pos_40 = pos_30 + (size_t)1U;
            first5 = sub[pos_30];
            pos_50 = pos_40 + (size_t)1U;
            first6 = sub[pos_40];
            first7 = sub[pos_50];
            n = (uint64_t)(uint32_t)first7;
            bfirst = (uint64_t)(uint32_t)first6;
            n1 = bfirst + n * 256ULL;
            bfirst1 = (uint64_t)(uint32_t)first5;
            n2 = bfirst1 + n1 * 256ULL;
            bfirst2 = (uint64_t)(uint32_t)first4;
            n3 = bfirst2 + n2 * 256ULL;
            bfirst3 = (uint64_t)(uint32_t)first3;
            n4 = bfirst3 + n3 * 256ULL;
            bfirst4 = (uint64_t)(uint32_t)first2;
            n5 = bfirst4 + n4 * 256ULL;
            bfirst5 = (uint64_t)(uint32_t)first1;
            n6 = bfirst5 + n5 * 256ULL;
            bfirst6 = (uint64_t)(uint32_t)first;
            tptr2 = bfirst6 + n6 * 256ULL;
            readOffset0 = 0ULL;
            writeOffset0 = 0ULL;
            failed = FALSE;
            ok = ProbeInit2("_MultiProbe.tptr2", (uint64_t)4U, DestT2);
            if (ok)
            {
              rd = readOffset0;
              wr2 = writeOffset0;
              ok1 = ProbeAndCopyAlt((uint64_t)4U, rd, wr2, tptr2, DestT2);
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
              ErrorHandlerFn("_MultiProbe",
                "tptr2",
                "probe",
                0ULL,
                Ctxt,
                EverParseStreamOf(DestT2),
                0ULL);
              b = 0ULL;
            }
            else
            {
              b = wr;
            }
            if (b != 0ULL)
            {
              base = EverParseStreamOf(DestT2);
              len = (size_t)EverParseStreamLen(DestT2);
              cursor = (size_t)0U;
              res6 = ProbeValidateCoreT((uint32_t)42U, Ctxt, ErrorHandlerFn, base, len, &cursor);
              actionSuccessTptr2 = res6 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
            }
            else
            {
              ErrorHandlerFn("_MultiProbe",
                "tptr2",
                EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
                EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
                  (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
                    EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                               : 15ULL,
                Ctxt,
                SlBase,
                fieldStarttptr2);
              actionSuccessTptr2 = FALSE;
            }
            resultAfterMultiProbe1 =
              actionSuccessTptr2 ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                                 : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
          }
          else
          {
            resultAfterMultiProbe1 = resultAftertptr2;
          }
          if (resultAfterMultiProbe1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
          {
            return resultAfterMultiProbe1;
          }
          ErrorHandlerFn("_MultiProbe",
            "tptr2",
            EverParsePulseInternalErrorReasonOfResult(resultAfterMultiProbe1),
            resultAfterMultiProbe1 == 0U ||
              (resultAfterMultiProbe1 >= 2U && resultAfterMultiProbe1 <= 8U) ? (uint64_t)(uint32_t)resultAfterMultiProbe1
                                                                             : 15ULL,
            Ctxt,
            SlBase,
            fieldStartMultiProbe1);
          return resultAfterMultiProbe1;
        }
        return resultAftertptr11;
      }
      return resultAftertag;
    }
    return resultAftersnd;
  }
  return resultAfterfst;
}

uint64_t
ProbeValidateMultiProbe(
  EVERPARSE_COPY_BUFFER_T DestT1,
  EVERPARSE_COPY_BUFFER_T DestT2,
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
  uint8_t
  status = ProbeValidateCoreMultiProbe(DestT1, DestT2, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreMaybeT(
  EVERPARSE_COPY_BUFFER_T Dest,
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
  size_t pos = (size_t)0U;
  size_t p = SlPos[0U];
  uint64_t viewStart = (uint64_t)p;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterBound;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  size_t pos_;
  uint8_t first1;
  size_t pos_1;
  uint8_t first2;
  uint8_t first3;
  uint32_t n;
  uint32_t bfirst;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t bound;
  size_t p2;
  uint64_t fieldStartMaybeT;
  size_t p3;
  uint64_t fieldStartptr;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterptr;
  uint8_t resultAfterMaybeT;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  uint8_t first4;
  size_t pos_2;
  uint8_t first5;
  size_t pos_3;
  uint8_t first6;
  size_t pos_4;
  uint8_t first7;
  size_t pos_5;
  uint8_t first8;
  size_t pos_6;
  uint8_t first9;
  size_t pos_7;
  uint8_t first10;
  uint8_t first11;
  uint64_t n3;
  uint64_t bfirst3;
  uint64_t n4;
  uint64_t bfirst4;
  uint64_t n5;
  uint64_t bfirst5;
  uint64_t n6;
  uint64_t bfirst6;
  uint64_t n7;
  uint64_t bfirst7;
  uint64_t n8;
  uint64_t bfirst8;
  uint64_t n9;
  uint64_t bfirst9;
  uint64_t ptr;
  BOOLEAN actionSuccessPtr;
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
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res1;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterBound = res;
  }
  else
  {
    ErrorHandlerFn("_MaybeT",
      "Bound",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterBound = res;
  }
  if (resultAfterBound == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)4U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    first = sub[0U];
    pos_ = (size_t)2U;
    first1 = sub[1U];
    pos_1 = pos_ + (size_t)1U;
    first2 = sub[pos_];
    first3 = sub[pos_1];
    n = (uint32_t)first3;
    bfirst = (uint32_t)first2;
    n1 = bfirst + n * 256U;
    bfirst1 = (uint32_t)first1;
    n2 = bfirst1 + n1 * 256U;
    bfirst2 = (uint32_t)first;
    bound = bfirst2 + n2 * 256U;
    p2 = SlPos[0U];
    fieldStartMaybeT = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStartptr = (uint64_t)p3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p02 = pos1;
    p4 = SlPos[0U];
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)8U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)8U;
      resultAfterptr = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterptr = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p03 = SlPos[0U];
      m1 = p03 + (size_t)8U;
      sub1 = SlBase + p03;
      SlPos[0U] = m1;
      first4 = sub1[0U];
      pos_2 = (size_t)2U;
      first5 = sub1[1U];
      pos_3 = pos_2 + (size_t)1U;
      first6 = sub1[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first7 = sub1[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first8 = sub1[pos_4];
      pos_6 = pos_5 + (size_t)1U;
      first9 = sub1[pos_5];
      pos_7 = pos_6 + (size_t)1U;
      first10 = sub1[pos_6];
      first11 = sub1[pos_7];
      n3 = (uint64_t)(uint32_t)first11;
      bfirst3 = (uint64_t)(uint32_t)first10;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first9;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first8;
      n6 = bfirst5 + n5 * 256ULL;
      bfirst6 = (uint64_t)(uint32_t)first7;
      n7 = bfirst6 + n6 * 256ULL;
      bfirst7 = (uint64_t)(uint32_t)first6;
      n8 = bfirst7 + n7 * 256ULL;
      bfirst8 = (uint64_t)(uint32_t)first5;
      n9 = bfirst8 + n8 * 256ULL;
      bfirst9 = (uint64_t)(uint32_t)first4;
      ptr = bfirst9 + n9 * 256ULL;
      if (ptr == 0ULL)
      {
        actionSuccessPtr = TRUE;
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
          ok1 = ProbeAndCopy2((uint64_t)4U, rd, wr0, ptr, Dest);
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
          base = EverParseStreamOf(Dest);
          len = (size_t)EverParseStreamLen(Dest);
          cursor = (size_t)0U;
          res1 = ProbeValidateCoreT(bound, Ctxt, ErrorHandlerFn, base, len, &cursor);
          actionSuccessPtr = res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          ErrorHandlerFn("_MaybeT",
            "ptr",
            EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
            EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
              (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
                EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                           : 15ULL,
            Ctxt,
            SlBase,
            fieldStartptr);
          actionSuccessPtr = FALSE;
        }
      }
      resultAfterMaybeT =
        actionSuccessPtr ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                         : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterMaybeT = resultAfterptr;
    }
    if (resultAfterMaybeT == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterMaybeT;
    }
    ErrorHandlerFn("_MaybeT",
      "ptr",
      EverParsePulseInternalErrorReasonOfResult(resultAfterMaybeT),
      resultAfterMaybeT == 0U || (resultAfterMaybeT >= 2U && resultAfterMaybeT <= 8U) ? (uint64_t)(uint32_t)resultAfterMaybeT
                                                                                      : 15ULL,
      Ctxt,
      SlBase,
      fieldStartMaybeT);
    return resultAfterMaybeT;
  }
  return resultAfterBound;
}

uint64_t
ProbeValidateMaybeT(
  EVERPARSE_COPY_BUFFER_T Dest,
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
  uint8_t status = ProbeValidateCoreMaybeT(Dest, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreCoercePtr(
  EVERPARSE_COPY_BUFFER_T Dest,
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
  size_t pos = (size_t)0U;
  size_t p = SlPos[0U];
  uint64_t viewStart = (uint64_t)p;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterBound;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  size_t pos_;
  uint8_t first1;
  size_t pos_1;
  uint8_t first2;
  uint8_t first3;
  uint32_t n;
  uint32_t bfirst;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t bound;
  size_t p2;
  uint64_t fieldStartCoercePtr;
  size_t p3;
  uint64_t fieldStartptr;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterptr;
  uint8_t resultAfterCoercePtr;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  uint8_t first4;
  size_t pos_2;
  uint8_t first5;
  size_t pos_3;
  uint8_t first6;
  uint8_t first7;
  uint32_t n3;
  uint32_t bfirst3;
  uint32_t n4;
  uint32_t bfirst4;
  uint32_t n5;
  uint32_t bfirst5;
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
  BOOLEAN actionSuccessPtr;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res1;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterBound = res;
  }
  else
  {
    ErrorHandlerFn("_CoercePtr",
      "Bound",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterBound = res;
  }
  if (resultAfterBound == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)4U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    first = sub[0U];
    pos_ = (size_t)2U;
    first1 = sub[1U];
    pos_1 = pos_ + (size_t)1U;
    first2 = sub[pos_];
    first3 = sub[pos_1];
    n = (uint32_t)first3;
    bfirst = (uint32_t)first2;
    n1 = bfirst + n * 256U;
    bfirst1 = (uint32_t)first1;
    n2 = bfirst1 + n1 * 256U;
    bfirst2 = (uint32_t)first;
    bound = bfirst2 + n2 * 256U;
    p2 = SlPos[0U];
    fieldStartCoercePtr = (uint64_t)p2;
    p3 = SlPos[0U];
    fieldStartptr = (uint64_t)p3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p4 = SlPos[0U];
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)4U;
      resultAfterptr = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterptr = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p03 = SlPos[0U];
      m1 = p03 + (size_t)4U;
      sub1 = SlBase + p03;
      SlPos[0U] = m1;
      first4 = sub1[0U];
      pos_2 = (size_t)2U;
      first5 = sub1[1U];
      pos_3 = pos_2 + (size_t)1U;
      first6 = sub1[pos_2];
      first7 = sub1[pos_3];
      n3 = (uint32_t)first7;
      bfirst3 = (uint32_t)first6;
      n4 = bfirst3 + n3 * 256U;
      bfirst4 = (uint32_t)first5;
      n5 = bfirst4 + n4 * 256U;
      bfirst5 = (uint32_t)first4;
      ptr = bfirst5 + n5 * 256U;
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
        base = EverParseStreamOf(Dest);
        len = (size_t)EverParseStreamLen(Dest);
        cursor = (size_t)0U;
        res1 = ProbeValidateCoreT(bound, Ctxt, ErrorHandlerFn, base, len, &cursor);
        actionSuccessPtr = res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        ErrorHandlerFn("_CoercePtr",
          "ptr",
          EverParsePulseInternalErrorReasonOfResult(EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED),
          EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED == 0U ||
            (EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED >= 2U &&
              EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED <= 8U) ? (uint64_t)(uint32_t)EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
                                                                         : 15ULL,
          Ctxt,
          SlBase,
          fieldStartptr);
        actionSuccessPtr = FALSE;
      }
      resultAfterCoercePtr =
        actionSuccessPtr ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                         : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterCoercePtr = resultAfterptr;
    }
    if (resultAfterCoercePtr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterCoercePtr;
    }
    ErrorHandlerFn("_CoercePtr",
      "ptr",
      EverParsePulseInternalErrorReasonOfResult(resultAfterCoercePtr),
      resultAfterCoercePtr == 0U || (resultAfterCoercePtr >= 2U && resultAfterCoercePtr <= 8U) ? (uint64_t)(uint32_t)resultAfterCoercePtr
                                                                                               : 15ULL,
      Ctxt,
      SlBase,
      fieldStartCoercePtr);
    return resultAfterCoercePtr;
  }
  return resultAfterBound;
}

uint64_t
ProbeValidateCoercePtr(
  EVERPARSE_COPY_BUFFER_T Dest,
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
  uint8_t status = ProbeValidateCoreCoercePtr(Dest, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreProbeOnly(
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
  size_t p = SlPos[0U];
  uint64_t fieldStartProbeOnly = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterProbeOnly;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)8U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterProbeOnly = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterProbeOnly = res;
  }
  if (resultAfterProbeOnly == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterProbeOnly;
  }
  ErrorHandlerFn("_ProbeOnly",
    "x",
    EverParsePulseInternalErrorReasonOfResult(resultAfterProbeOnly),
    resultAfterProbeOnly == 0U || (resultAfterProbeOnly >= 2U && resultAfterProbeOnly <= 8U) ? (uint64_t)(uint32_t)resultAfterProbeOnly
                                                                                             : 15ULL,
    Ctxt,
    SlBase,
    fieldStartProbeOnly);
  return resultAfterProbeOnly;
}

uint64_t
ProbeValidateProbeOnly(
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
  uint8_t status = ProbeValidateCoreProbeOnly(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreBothEntrypoints(
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
  size_t p = SlPos[0U];
  uint64_t fieldStartBothEntrypoints = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterBothEntrypoints;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)8U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterBothEntrypoints = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterBothEntrypoints = res;
  }
  if (resultAfterBothEntrypoints == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterBothEntrypoints;
  }
  ErrorHandlerFn("_BothEntrypoints",
    "x",
    EverParsePulseInternalErrorReasonOfResult(resultAfterBothEntrypoints),
    resultAfterBothEntrypoints == 0U ||
      (resultAfterBothEntrypoints >= 2U && resultAfterBothEntrypoints <= 8U) ? (uint64_t)(uint32_t)resultAfterBothEntrypoints
                                                                             : 15ULL,
    Ctxt,
    SlBase,
    fieldStartBothEntrypoints);
  return resultAfterBothEntrypoints;
}

uint64_t
ProbeValidateBothEntrypoints(
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
  uint8_t status = ProbeValidateCoreBothEntrypoints(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreNamedPlainEp(
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
  size_t p = SlPos[0U];
  uint64_t fieldStartNamedPlainEp = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterNamedPlainEp;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)8U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterNamedPlainEp = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterNamedPlainEp = res;
  }
  if (resultAfterNamedPlainEp == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterNamedPlainEp;
  }
  ErrorHandlerFn("_NamedPlainEp",
    "x",
    EverParsePulseInternalErrorReasonOfResult(resultAfterNamedPlainEp),
    resultAfterNamedPlainEp == 0U ||
      (resultAfterNamedPlainEp >= 2U && resultAfterNamedPlainEp <= 8U) ? (uint64_t)(uint32_t)resultAfterNamedPlainEp
                                                                       : 15ULL,
    Ctxt,
    SlBase,
    fieldStartNamedPlainEp);
  return resultAfterNamedPlainEp;
}

uint64_t
ProbeValidateNamedPlainEp(
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
  uint8_t status = ProbeValidateCoreNamedPlainEp(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreNamedProbeEp(
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
  size_t p = SlPos[0U];
  uint64_t fieldStartNamedProbeEp = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterNamedProbeEp;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)8U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterNamedProbeEp = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterNamedProbeEp = res;
  }
  if (resultAfterNamedProbeEp == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterNamedProbeEp;
  }
  ErrorHandlerFn("_NamedProbeEp",
    "x",
    EverParsePulseInternalErrorReasonOfResult(resultAfterNamedProbeEp),
    resultAfterNamedProbeEp == 0U ||
      (resultAfterNamedProbeEp >= 2U && resultAfterNamedProbeEp <= 8U) ? (uint64_t)(uint32_t)resultAfterNamedProbeEp
                                                                       : 15ULL,
    Ctxt,
    SlBase,
    fieldStartNamedProbeEp);
  return resultAfterNamedProbeEp;
}

uint64_t
ProbeValidateNamedProbeEp(
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
  uint8_t status = ProbeValidateCoreNamedProbeEp(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ProbeValidateCoreNamedBothEp(
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
  size_t p = SlPos[0U];
  uint64_t fieldStartNamedBothEp = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterNamedBothEp;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)8U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterNamedBothEp = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterNamedBothEp = res;
  }
  if (resultAfterNamedBothEp == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterNamedBothEp;
  }
  ErrorHandlerFn("_NamedBothEp",
    "x",
    EverParsePulseInternalErrorReasonOfResult(resultAfterNamedBothEp),
    resultAfterNamedBothEp == 0U || (resultAfterNamedBothEp >= 2U && resultAfterNamedBothEp <= 8U) ? (uint64_t)(uint32_t)resultAfterNamedBothEp
                                                                                                   : 15ULL,
    Ctxt,
    SlBase,
    fieldStartNamedBothEp);
  return resultAfterNamedBothEp;
}

uint64_t
ProbeValidateNamedBothEp(
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
  uint8_t status = ProbeValidateCoreNamedBothEp(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

