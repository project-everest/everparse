

#include "Probe.h"

#include "Probe_ExternalAPI.h"

static inline uint8_t
ValidateCoreT(
  uint32_t Bound,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartT = (uint64_t)p1;
  uint64_t startPositionT = fieldStartT;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)2U <= (rem0 - p00);
  uint8_t resultAfterx;
  uint8_t resultAfterT;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t first0;
  uint8_t first10;
  uint16_t n0;
  uint16_t bfirst0;
  uint16_t res0;
  uint16_t x;
  BOOLEAN xConstraintIsOk;
  size_t p3;
  uint64_t fieldStartT1;
  uint64_t startPositionT1;
  size_t pos1;
  size_t p02;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftery_refinement;
  uint8_t resultAfterT0;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t first;
  uint8_t first1;
  uint16_t n;
  uint16_t bfirst;
  uint16_t res;
  uint16_t y_refinement;
  BOOLEAN y_refinementConstraintIsOk;
  if (hasBytes0)
  {
    pos = p00 + (size_t)2U;
    resultAfterx = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterx = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterx == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)2U;
    sub0 = SlBase + p01;
    pos_ = (size_t)1U;
    first0 = sub0[0U];
    first10 = sub0[pos_];
    n0 = (uint16_t)(uint32_t)first10;
    bfirst0 = (uint16_t)(uint32_t)first0;
    res0 = (uint32_t)bfirst0 + (uint32_t)n0 * 256U;
    *SlPos = m0;
    x = res0;
    xConstraintIsOk = (uint32_t)x >= Bound;
    if (xConstraintIsOk)
    {
      /* Validating field y */
      p3 = *SlPos;
      fieldStartT1 = (uint64_t)p3;
      startPositionT1 = fieldStartT1;
      pos1 = (size_t)0U;
      /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
      p02 = pos1;
      p = *SlPos;
      rem = SlLen - p;
      hasBytes = p02 <= rem && (size_t)2U <= (rem - p02);
      if (hasBytes)
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
        p0 = *SlPos;
        m = p0 + (size_t)2U;
        sub = SlBase + p0;
        pos_0 = (size_t)1U;
        first = sub[0U];
        first1 = sub[pos_0];
        n = (uint16_t)(uint32_t)first1;
        bfirst = (uint16_t)(uint32_t)first;
        res = (uint32_t)bfirst + (uint32_t)n * 256U;
        *SlPos = m;
        y_refinement = res;
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
          startPositionT1);
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
    startPositionT);
  return resultAfterT;
}

static uint8_t
ValidateCoreS(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos = (size_t)0U;
  size_t p1 = *SlPos;
  uint64_t viewStart = (uint64_t)p1;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)1U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterbound;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  uint8_t res1;
  uint8_t bound;
  size_t p3;
  uint64_t fieldStartS;
  uint64_t startPositionS;
  size_t p4;
  uint64_t fieldStarttpointer;
  size_t pos1;
  size_t p02;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftertpointer;
  uint8_t resultAfterS;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_;
  uint8_t first;
  size_t pos_1;
  uint8_t first1;
  size_t pos_2;
  uint8_t first2;
  size_t pos_3;
  uint8_t first3;
  size_t pos_4;
  uint8_t first4;
  size_t pos_5;
  uint8_t first5;
  size_t pos_6;
  uint8_t first6;
  uint8_t first7;
  uint64_t n0;
  uint64_t bfirst0;
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
  uint64_t n;
  uint64_t bfirst;
  uint64_t res2;
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
  BOOLEAN actionSuccessTpointer;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (hasBytes0)
  {
    pos = p00 + (size_t)1U;
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterbound = res0;
  }
  else
  {
    ErrorHandlerFn("_S",
      "bound",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterbound = res0;
  }
  if (resultAfterbound == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)1U;
    sub0 = SlBase + p01;
    res1 = sub0[0U];
    *SlPos = m0;
    bound = res1;
    p3 = *SlPos;
    fieldStartS = (uint64_t)p3;
    startPositionS = fieldStartS;
    p4 = *SlPos;
    fieldStarttpointer = (uint64_t)p4;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p02 = pos1;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p02 <= rem && (size_t)8U <= (rem - p02);
    if (hasBytes)
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
      p0 = *SlPos;
      m = p0 + (size_t)8U;
      sub = SlBase + p0;
      pos_ = (size_t)1U;
      first = sub[0U];
      pos_1 = pos_ + (size_t)1U;
      first1 = sub[pos_];
      pos_2 = pos_1 + (size_t)1U;
      first2 = sub[pos_1];
      pos_3 = pos_2 + (size_t)1U;
      first3 = sub[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first4 = sub[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first5 = sub[pos_4];
      pos_6 = pos_5 + (size_t)1U;
      first6 = sub[pos_5];
      first7 = sub[pos_6];
      n0 = (uint64_t)(uint32_t)first7;
      bfirst0 = (uint64_t)(uint32_t)first6;
      n1 = bfirst0 + n0 * 256ULL;
      bfirst1 = (uint64_t)(uint32_t)first5;
      n2 = bfirst1 + n1 * 256ULL;
      bfirst2 = (uint64_t)(uint32_t)first4;
      n3 = bfirst2 + n2 * 256ULL;
      bfirst3 = (uint64_t)(uint32_t)first3;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first2;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first1;
      n = bfirst5 + n5 * 256ULL;
      bfirst = (uint64_t)(uint32_t)first;
      res2 = bfirst + n * 256ULL;
      *SlPos = m;
      tpointer = res2;
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
        base = EverParseStreamOf(Dest);
        len = (size_t)EverParseStreamLen(Dest);
        cursor = (size_t)0U;
        res = ValidateCoreT((uint32_t)bound, Ctxt, ErrorHandlerFn, base, len, &cursor);
        actionSuccessTpointer = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
      startPositionS);
    return resultAfterS;
  }
  return resultAfterbound;
}

uint64_t
ProbeValidateS(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreS(Dest, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreU(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos0 = (size_t)0U;
  /* Validating field tag */
  size_t p1 = *SlPos;
  uint64_t viewStart = (uint64_t)p1;
  size_t fieldOff = pos0;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t p00 = pos0;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)1U <= (rem0 - p00);
  uint8_t res0;
  uint8_t res1;
  uint8_t resultAftertag;
  size_t consumed;
  size_t p3;
  size_t p_;
  size_t p4;
  uint64_t fieldStartU;
  uint64_t startPositionU;
  size_t p5;
  uint64_t fieldStartspointer;
  size_t pos;
  size_t p01;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAfterspointer;
  uint8_t resultAfterU;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_;
  uint8_t first;
  size_t pos_1;
  uint8_t first1;
  size_t pos_2;
  uint8_t first2;
  size_t pos_3;
  uint8_t first3;
  size_t pos_4;
  uint8_t first4;
  size_t pos_5;
  uint8_t first5;
  size_t pos_6;
  uint8_t first6;
  uint8_t first7;
  uint64_t n0;
  uint64_t bfirst0;
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
  uint64_t n;
  uint64_t bfirst;
  uint64_t res2;
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
  BOOLEAN actionSuccessSpointer;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (hasBytes0)
  {
    pos0 = p00 + (size_t)1U;
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res1 = res0;
  }
  else
  {
    ErrorHandlerFn("_U",
      "tag",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    res1 = res0;
  }
  if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos0;
    p3 = *SlPos;
    p_ = p3 + consumed;
    *SlPos = p_;
    resultAftertag = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftertag = res1;
  }
  if (resultAftertag == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p4 = *SlPos;
    fieldStartU = (uint64_t)p4;
    startPositionU = fieldStartU;
    p5 = *SlPos;
    fieldStartspointer = (uint64_t)p5;
    pos = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p01 = pos;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p01 <= rem && (size_t)8U <= (rem - p01);
    if (hasBytes)
    {
      pos = p01 + (size_t)8U;
      resultAfterspointer = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterspointer = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterspointer == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p0 = *SlPos;
      m = p0 + (size_t)8U;
      sub = SlBase + p0;
      pos_ = (size_t)1U;
      first = sub[0U];
      pos_1 = pos_ + (size_t)1U;
      first1 = sub[pos_];
      pos_2 = pos_1 + (size_t)1U;
      first2 = sub[pos_1];
      pos_3 = pos_2 + (size_t)1U;
      first3 = sub[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first4 = sub[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first5 = sub[pos_4];
      pos_6 = pos_5 + (size_t)1U;
      first6 = sub[pos_5];
      first7 = sub[pos_6];
      n0 = (uint64_t)(uint32_t)first7;
      bfirst0 = (uint64_t)(uint32_t)first6;
      n1 = bfirst0 + n0 * 256ULL;
      bfirst1 = (uint64_t)(uint32_t)first5;
      n2 = bfirst1 + n1 * 256ULL;
      bfirst2 = (uint64_t)(uint32_t)first4;
      n3 = bfirst2 + n2 * 256ULL;
      bfirst3 = (uint64_t)(uint32_t)first3;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first2;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first1;
      n = bfirst5 + n5 * 256ULL;
      bfirst = (uint64_t)(uint32_t)first;
      res2 = bfirst + n * 256ULL;
      *SlPos = m;
      spointer = res2;
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
        base = EverParseStreamOf(DestS);
        len = (size_t)EverParseStreamLen(DestS);
        cursor = (size_t)0U;
        res = ValidateCoreS(DestT, Ctxt, ErrorHandlerFn, base, len, &cursor);
        actionSuccessSpointer = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
      startPositionU);
    return resultAfterU;
  }
  return resultAftertag;
}

uint64_t
ProbeValidateU(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreU(DestS, DestT, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreV(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos = (size_t)0U;
  size_t p1 = *SlPos;
  uint64_t viewStart = (uint64_t)p1;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)1U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAftertag;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  uint8_t res1;
  uint8_t tag;
  size_t p3;
  uint64_t fieldStartV;
  uint64_t startPositionV;
  size_t p4;
  uint64_t fieldStartsptr;
  size_t pos10;
  size_t p02;
  size_t p5;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAftersptr0;
  uint8_t resultAfterV;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  size_t pos_;
  uint8_t first0;
  size_t pos_1;
  uint8_t first10;
  size_t pos_2;
  uint8_t first20;
  size_t pos_3;
  uint8_t first30;
  size_t pos_4;
  uint8_t first40;
  size_t pos_5;
  uint8_t first50;
  size_t pos_6;
  uint8_t first60;
  uint8_t first70;
  uint64_t n0;
  uint64_t bfirst0;
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
  uint64_t res2;
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
  BOOLEAN actionSuccessSptr;
  uint8_t *base0;
  size_t len0;
  size_t cursor0;
  uint8_t res3;
  uint8_t resultAftersptr;
  size_t p6;
  uint64_t fieldStartV0;
  uint64_t startPositionV0;
  size_t p7;
  uint64_t fieldStarttptr;
  size_t pos11;
  size_t p04;
  size_t p8;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t resultAftertptr0;
  uint8_t resultAfterV0;
  size_t p05;
  size_t m2;
  uint8_t *sub2;
  size_t pos_0;
  uint8_t first8;
  size_t pos_10;
  uint8_t first11;
  size_t pos_20;
  uint8_t first21;
  size_t pos_30;
  uint8_t first31;
  size_t pos_40;
  uint8_t first41;
  size_t pos_50;
  uint8_t first51;
  size_t pos_60;
  uint8_t first61;
  uint8_t first71;
  uint64_t n7;
  uint64_t bfirst7;
  uint64_t n8;
  uint64_t bfirst8;
  uint64_t n9;
  uint64_t bfirst9;
  uint64_t n10;
  uint64_t bfirst10;
  uint64_t n11;
  uint64_t bfirst11;
  uint64_t n12;
  uint64_t bfirst12;
  uint64_t n13;
  uint64_t bfirst13;
  uint64_t res4;
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
  BOOLEAN actionSuccessTptr;
  uint8_t *base1;
  size_t len1;
  size_t cursor1;
  uint8_t res5;
  uint8_t resultAftertptr;
  size_t p9;
  uint64_t fieldStartV1;
  uint64_t startPositionV1;
  size_t p10;
  uint64_t fieldStartt2ptr;
  size_t pos1;
  size_t p06;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftert2ptr;
  uint8_t resultAfterV1;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_7;
  uint8_t first;
  size_t pos_11;
  uint8_t first1;
  size_t pos_21;
  uint8_t first2;
  size_t pos_31;
  uint8_t first3;
  size_t pos_41;
  uint8_t first4;
  size_t pos_51;
  uint8_t first5;
  size_t pos_61;
  uint8_t first6;
  uint8_t first7;
  uint64_t n14;
  uint64_t bfirst14;
  uint64_t n15;
  uint64_t bfirst15;
  uint64_t n16;
  uint64_t bfirst16;
  uint64_t n17;
  uint64_t bfirst17;
  uint64_t n18;
  uint64_t bfirst18;
  uint64_t n19;
  uint64_t bfirst19;
  uint64_t n;
  uint64_t bfirst;
  uint64_t res6;
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
  BOOLEAN actionSuccessT2ptr;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (hasBytes0)
  {
    pos = p00 + (size_t)1U;
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAftertag = res0;
  }
  else
  {
    ErrorHandlerFn("_V",
      "tag",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAftertag = res0;
  }
  if (resultAftertag == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)1U;
    sub0 = SlBase + p01;
    res1 = sub0[0U];
    *SlPos = m0;
    tag = res1;
    p3 = *SlPos;
    fieldStartV = (uint64_t)p3;
    startPositionV = fieldStartV;
    p4 = *SlPos;
    fieldStartsptr = (uint64_t)p4;
    pos10 = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p02 = pos10;
    p5 = *SlPos;
    rem1 = SlLen - p5;
    hasBytes1 = p02 <= rem1 && (size_t)8U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos10 = p02 + (size_t)8U;
      resultAftersptr0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftersptr0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftersptr0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p03 = *SlPos;
      m1 = p03 + (size_t)8U;
      sub1 = SlBase + p03;
      pos_ = (size_t)1U;
      first0 = sub1[0U];
      pos_1 = pos_ + (size_t)1U;
      first10 = sub1[pos_];
      pos_2 = pos_1 + (size_t)1U;
      first20 = sub1[pos_1];
      pos_3 = pos_2 + (size_t)1U;
      first30 = sub1[pos_2];
      pos_4 = pos_3 + (size_t)1U;
      first40 = sub1[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first50 = sub1[pos_4];
      pos_6 = pos_5 + (size_t)1U;
      first60 = sub1[pos_5];
      first70 = sub1[pos_6];
      n0 = (uint64_t)(uint32_t)first70;
      bfirst0 = (uint64_t)(uint32_t)first60;
      n1 = bfirst0 + n0 * 256ULL;
      bfirst1 = (uint64_t)(uint32_t)first50;
      n2 = bfirst1 + n1 * 256ULL;
      bfirst2 = (uint64_t)(uint32_t)first40;
      n3 = bfirst2 + n2 * 256ULL;
      bfirst3 = (uint64_t)(uint32_t)first30;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first20;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first10;
      n6 = bfirst5 + n5 * 256ULL;
      bfirst6 = (uint64_t)(uint32_t)first0;
      res2 = bfirst6 + n6 * 256ULL;
      *SlPos = m1;
      sptr = res2;
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
        base0 = EverParseStreamOf(DestS);
        len0 = (size_t)EverParseStreamLen(DestS);
        cursor0 = (size_t)0U;
        res3 = ValidateCoreS(DestT, Ctxt, ErrorHandlerFn, base0, len0, &cursor0);
        actionSuccessSptr = res3 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
      resultAfterV = resultAftersptr0;
    }
    if (resultAfterV == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      resultAftersptr = resultAfterV;
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
        startPositionV);
      resultAftersptr = resultAfterV;
    }
    if (resultAftersptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p6 = *SlPos;
      fieldStartV0 = (uint64_t)p6;
      startPositionV0 = fieldStartV0;
      p7 = *SlPos;
      fieldStarttptr = (uint64_t)p7;
      pos11 = (size_t)0U;
      /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
      p04 = pos11;
      p8 = *SlPos;
      rem2 = SlLen - p8;
      hasBytes2 = p04 <= rem2 && (size_t)8U <= (rem2 - p04);
      if (hasBytes2)
      {
        pos11 = p04 + (size_t)8U;
        resultAftertptr0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAftertptr0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (resultAftertptr0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        p05 = *SlPos;
        m2 = p05 + (size_t)8U;
        sub2 = SlBase + p05;
        pos_0 = (size_t)1U;
        first8 = sub2[0U];
        pos_10 = pos_0 + (size_t)1U;
        first11 = sub2[pos_0];
        pos_20 = pos_10 + (size_t)1U;
        first21 = sub2[pos_10];
        pos_30 = pos_20 + (size_t)1U;
        first31 = sub2[pos_20];
        pos_40 = pos_30 + (size_t)1U;
        first41 = sub2[pos_30];
        pos_50 = pos_40 + (size_t)1U;
        first51 = sub2[pos_40];
        pos_60 = pos_50 + (size_t)1U;
        first61 = sub2[pos_50];
        first71 = sub2[pos_60];
        n7 = (uint64_t)(uint32_t)first71;
        bfirst7 = (uint64_t)(uint32_t)first61;
        n8 = bfirst7 + n7 * 256ULL;
        bfirst8 = (uint64_t)(uint32_t)first51;
        n9 = bfirst8 + n8 * 256ULL;
        bfirst9 = (uint64_t)(uint32_t)first41;
        n10 = bfirst9 + n9 * 256ULL;
        bfirst10 = (uint64_t)(uint32_t)first31;
        n11 = bfirst10 + n10 * 256ULL;
        bfirst11 = (uint64_t)(uint32_t)first21;
        n12 = bfirst11 + n11 * 256ULL;
        bfirst12 = (uint64_t)(uint32_t)first11;
        n13 = bfirst12 + n12 * 256ULL;
        bfirst13 = (uint64_t)(uint32_t)first8;
        res4 = bfirst13 + n13 * 256ULL;
        *SlPos = m2;
        tptr = res4;
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
          base1 = EverParseStreamOf(DestT);
          len1 = (size_t)EverParseStreamLen(DestT);
          cursor1 = (size_t)0U;
          res5 = ValidateCoreT((uint32_t)17U, Ctxt, ErrorHandlerFn, base1, len1, &cursor1);
          actionSuccessTptr = res5 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
        resultAfterV0 =
          actionSuccessTptr ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                            : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
      }
      else
      {
        resultAfterV0 = resultAftertptr0;
      }
      if (resultAfterV0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        resultAftertptr = resultAfterV0;
      }
      else
      {
        ErrorHandlerFn("_V",
          "tptr",
          EverParsePulseInternalErrorReasonOfResult(resultAfterV0),
          resultAfterV0 == 0U || (resultAfterV0 >= 2U && resultAfterV0 <= 8U) ? (uint64_t)(uint32_t)resultAfterV0
                                                                              : 15ULL,
          Ctxt,
          SlBase,
          startPositionV0);
        resultAftertptr = resultAfterV0;
      }
      if (resultAftertptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        p9 = *SlPos;
        fieldStartV1 = (uint64_t)p9;
        startPositionV1 = fieldStartV1;
        p10 = *SlPos;
        fieldStartt2ptr = (uint64_t)p10;
        pos1 = (size_t)0U;
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        p06 = pos1;
        p = *SlPos;
        rem = SlLen - p;
        hasBytes = p06 <= rem && (size_t)8U <= (rem - p06);
        if (hasBytes)
        {
          pos1 = p06 + (size_t)8U;
          resultAftert2ptr = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAftert2ptr = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (resultAftert2ptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          p0 = *SlPos;
          m = p0 + (size_t)8U;
          sub = SlBase + p0;
          pos_7 = (size_t)1U;
          first = sub[0U];
          pos_11 = pos_7 + (size_t)1U;
          first1 = sub[pos_7];
          pos_21 = pos_11 + (size_t)1U;
          first2 = sub[pos_11];
          pos_31 = pos_21 + (size_t)1U;
          first3 = sub[pos_21];
          pos_41 = pos_31 + (size_t)1U;
          first4 = sub[pos_31];
          pos_51 = pos_41 + (size_t)1U;
          first5 = sub[pos_41];
          pos_61 = pos_51 + (size_t)1U;
          first6 = sub[pos_51];
          first7 = sub[pos_61];
          n14 = (uint64_t)(uint32_t)first7;
          bfirst14 = (uint64_t)(uint32_t)first6;
          n15 = bfirst14 + n14 * 256ULL;
          bfirst15 = (uint64_t)(uint32_t)first5;
          n16 = bfirst15 + n15 * 256ULL;
          bfirst16 = (uint64_t)(uint32_t)first4;
          n17 = bfirst16 + n16 * 256ULL;
          bfirst17 = (uint64_t)(uint32_t)first3;
          n18 = bfirst17 + n17 * 256ULL;
          bfirst18 = (uint64_t)(uint32_t)first2;
          n19 = bfirst18 + n18 * 256ULL;
          bfirst19 = (uint64_t)(uint32_t)first1;
          n = bfirst19 + n19 * 256ULL;
          bfirst = (uint64_t)(uint32_t)first;
          res6 = bfirst + n * 256ULL;
          *SlPos = m;
          t2ptr = res6;
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
            base = EverParseStreamOf(DestT);
            len = (size_t)EverParseStreamLen(DestT);
            cursor = (size_t)0U;
            res = ValidateCoreT((uint32_t)tag, Ctxt, ErrorHandlerFn, base, len, &cursor);
            actionSuccessT2ptr = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
          resultAfterV1 =
            actionSuccessT2ptr ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                               : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
        }
        else
        {
          resultAfterV1 = resultAftert2ptr;
        }
        if (resultAfterV1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          return resultAfterV1;
        }
        ErrorHandlerFn("_V",
          "t2ptr",
          EverParsePulseInternalErrorReasonOfResult(resultAfterV1),
          resultAfterV1 == 0U || (resultAfterV1 >= 2U && resultAfterV1 <= 8U) ? (uint64_t)(uint32_t)resultAfterV1
                                                                              : 15ULL,
          Ctxt,
          SlBase,
          startPositionV1);
        return resultAfterV1;
      }
      return resultAftertptr;
    }
    return resultAftersptr;
  }
  return resultAftertag;
}

uint64_t
ProbeValidateV(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreV(DestS, DestT, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreIndirect(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartIndirect = (uint64_t)p1;
  uint64_t startPositionIndirect = fieldStartIndirect;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)9U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterIndirect;
  size_t consumed;
  size_t p;
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
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
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
    startPositionIndirect);
  return resultAfterIndirect;
}

uint64_t
ProbeValidateIndirect(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreIndirect(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static inline uint8_t
ValidateCoreTt(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartTt = (uint64_t)p1;
  uint64_t startPositionTt = fieldStartTt;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)9U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterTt;
  size_t consumed;
  size_t p;
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
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
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
    startPositionTt);
  return resultAfterTt;
}

static uint8_t
ValidateCoreI(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartI = (uint64_t)p1;
  uint64_t startPositionI = fieldStartI;
  size_t p2 = *SlPos;
  uint64_t fieldStartttptr = (uint64_t)p2;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
  size_t p00 = pos;
  size_t p = *SlPos;
  size_t rem = SlLen - p;
  BOOLEAN hasBytes = p00 <= rem && (size_t)8U <= (rem - p00);
  uint8_t resultAfterttptr;
  uint8_t resultAfterI;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_;
  uint8_t first;
  size_t pos_1;
  uint8_t first1;
  size_t pos_2;
  uint8_t first2;
  size_t pos_3;
  uint8_t first3;
  size_t pos_4;
  uint8_t first4;
  size_t pos_5;
  uint8_t first5;
  size_t pos_6;
  uint8_t first6;
  uint8_t first7;
  uint64_t n0;
  uint64_t bfirst0;
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
  uint64_t n;
  uint64_t bfirst;
  uint64_t res0;
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
  BOOLEAN actionSuccessTtptr;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (hasBytes)
  {
    pos = p00 + (size_t)8U;
    resultAfterttptr = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterttptr = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterttptr == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p0 = *SlPos;
    m = p0 + (size_t)8U;
    sub = SlBase + p0;
    pos_ = (size_t)1U;
    first = sub[0U];
    pos_1 = pos_ + (size_t)1U;
    first1 = sub[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first2 = sub[pos_1];
    pos_3 = pos_2 + (size_t)1U;
    first3 = sub[pos_2];
    pos_4 = pos_3 + (size_t)1U;
    first4 = sub[pos_3];
    pos_5 = pos_4 + (size_t)1U;
    first5 = sub[pos_4];
    pos_6 = pos_5 + (size_t)1U;
    first6 = sub[pos_5];
    first7 = sub[pos_6];
    n0 = (uint64_t)(uint32_t)first7;
    bfirst0 = (uint64_t)(uint32_t)first6;
    n1 = bfirst0 + n0 * 256ULL;
    bfirst1 = (uint64_t)(uint32_t)first5;
    n2 = bfirst1 + n1 * 256ULL;
    bfirst2 = (uint64_t)(uint32_t)first4;
    n3 = bfirst2 + n2 * 256ULL;
    bfirst3 = (uint64_t)(uint32_t)first3;
    n4 = bfirst3 + n3 * 256ULL;
    bfirst4 = (uint64_t)(uint32_t)first2;
    n5 = bfirst4 + n4 * 256ULL;
    bfirst5 = (uint64_t)(uint32_t)first1;
    n = bfirst5 + n5 * 256ULL;
    bfirst = (uint64_t)(uint32_t)first;
    res0 = bfirst + n * 256ULL;
    *SlPos = m;
    ttptr = res0;
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
      base = EverParseStreamOf(Dest);
      len = (size_t)EverParseStreamLen(Dest);
      cursor = (size_t)0U;
      res = ValidateCoreTt(Ctxt, ErrorHandlerFn, base, len, &cursor);
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
    startPositionI);
  return resultAfterI;
}

uint64_t
ProbeValidateI(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreI(Dest, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreMultiProbe(
  EVERPARSE_COPY_BUFFER_T DestT1,
  EVERPARSE_COPY_BUFFER_T DestT2,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos0 = (size_t)0U;
  /* Validating field fst */
  size_t p1 = *SlPos;
  uint64_t viewStart = (uint64_t)p1;
  size_t fieldOff = pos0;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos0;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t res0;
  uint8_t res1;
  uint8_t resultAfterfst;
  size_t consumed0;
  size_t p3;
  size_t p_;
  size_t pos1;
  size_t p4;
  uint64_t viewStart0;
  size_t fieldOff0;
  uint64_t startPos0;
  size_t p01;
  size_t p5;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res2;
  uint8_t res3;
  uint8_t resultAftersnd;
  size_t consumed1;
  size_t p6;
  size_t p_0;
  size_t pos2;
  size_t p7;
  uint64_t viewStart1;
  size_t fieldOff1;
  uint64_t startPos1;
  size_t p02;
  size_t p8;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t res4;
  uint8_t res5;
  uint8_t resultAftertag;
  size_t consumed;
  size_t p9;
  size_t p_1;
  size_t p10;
  uint64_t fieldStartMultiProbe;
  uint64_t startPositionMultiProbe;
  size_t p11;
  uint64_t fieldStarttptr1;
  size_t pos3;
  size_t p03;
  size_t p12;
  size_t rem3;
  BOOLEAN hasBytes3;
  uint8_t resultAftertptr10;
  uint8_t resultAfterMultiProbe;
  size_t p04;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t first0;
  size_t pos_1;
  uint8_t first10;
  size_t pos_2;
  uint8_t first20;
  size_t pos_3;
  uint8_t first30;
  size_t pos_4;
  uint8_t first40;
  size_t pos_5;
  uint8_t first50;
  size_t pos_6;
  uint8_t first60;
  uint8_t first70;
  uint64_t n0;
  uint64_t bfirst0;
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
  uint64_t res6;
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
  BOOLEAN actionSuccessTptr1;
  uint8_t *base0;
  size_t len0;
  size_t cursor0;
  uint8_t res7;
  uint8_t resultAftertptr1;
  size_t p13;
  uint64_t fieldStartMultiProbe0;
  uint64_t startPositionMultiProbe0;
  size_t p14;
  uint64_t fieldStarttptr2;
  size_t pos;
  size_t p05;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftertptr2;
  uint8_t resultAfterMultiProbe0;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t first;
  size_t pos_10;
  uint8_t first1;
  size_t pos_20;
  uint8_t first2;
  size_t pos_30;
  uint8_t first3;
  size_t pos_40;
  uint8_t first4;
  size_t pos_50;
  uint8_t first5;
  size_t pos_60;
  uint8_t first6;
  uint8_t first7;
  uint64_t n7;
  uint64_t bfirst7;
  uint64_t n8;
  uint64_t bfirst8;
  uint64_t n9;
  uint64_t bfirst9;
  uint64_t n10;
  uint64_t bfirst10;
  uint64_t n11;
  uint64_t bfirst11;
  uint64_t n12;
  uint64_t bfirst12;
  uint64_t n;
  uint64_t bfirst;
  uint64_t res8;
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
  BOOLEAN actionSuccessTptr2;
  uint8_t *base;
  size_t len;
  size_t cursor;
  uint8_t res;
  if (hasBytes0)
  {
    pos0 = p00 + (size_t)4U;
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    res1 = res0;
  }
  else
  {
    ErrorHandlerFn("_MultiProbe",
      "fst",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    res1 = res0;
  }
  if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed0 = pos0;
    p3 = *SlPos;
    p_ = p3 + consumed0;
    *SlPos = p_;
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
    p4 = *SlPos;
    viewStart0 = (uint64_t)p4;
    fieldOff0 = pos1;
    startPos0 = viewStart0 + (uint64_t)fieldOff0;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p01 = pos1;
    p5 = *SlPos;
    rem1 = SlLen - p5;
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
        startPos0);
      res3 = res2;
    }
    if (res3 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed1 = pos1;
      p6 = *SlPos;
      p_0 = p6 + consumed1;
      *SlPos = p_0;
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
      p7 = *SlPos;
      viewStart1 = (uint64_t)p7;
      fieldOff1 = pos2;
      startPos1 = viewStart1 + (uint64_t)fieldOff1;
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      p02 = pos2;
      p8 = *SlPos;
      rem2 = SlLen - p8;
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
          startPos1);
        res5 = res4;
      }
      if (res5 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        consumed = pos2;
        p9 = *SlPos;
        p_1 = p9 + consumed;
        *SlPos = p_1;
        resultAftertag = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAftertag = res5;
      }
      if (resultAftertag == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        p10 = *SlPos;
        fieldStartMultiProbe = (uint64_t)p10;
        startPositionMultiProbe = fieldStartMultiProbe;
        p11 = *SlPos;
        fieldStarttptr1 = (uint64_t)p11;
        pos3 = (size_t)0U;
        /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
        p03 = pos3;
        p12 = *SlPos;
        rem3 = SlLen - p12;
        hasBytes3 = p03 <= rem3 && (size_t)8U <= (rem3 - p03);
        if (hasBytes3)
        {
          pos3 = p03 + (size_t)8U;
          resultAftertptr10 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAftertptr10 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (resultAftertptr10 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          p04 = *SlPos;
          m0 = p04 + (size_t)8U;
          sub0 = SlBase + p04;
          pos_ = (size_t)1U;
          first0 = sub0[0U];
          pos_1 = pos_ + (size_t)1U;
          first10 = sub0[pos_];
          pos_2 = pos_1 + (size_t)1U;
          first20 = sub0[pos_1];
          pos_3 = pos_2 + (size_t)1U;
          first30 = sub0[pos_2];
          pos_4 = pos_3 + (size_t)1U;
          first40 = sub0[pos_3];
          pos_5 = pos_4 + (size_t)1U;
          first50 = sub0[pos_4];
          pos_6 = pos_5 + (size_t)1U;
          first60 = sub0[pos_5];
          first70 = sub0[pos_6];
          n0 = (uint64_t)(uint32_t)first70;
          bfirst0 = (uint64_t)(uint32_t)first60;
          n1 = bfirst0 + n0 * 256ULL;
          bfirst1 = (uint64_t)(uint32_t)first50;
          n2 = bfirst1 + n1 * 256ULL;
          bfirst2 = (uint64_t)(uint32_t)first40;
          n3 = bfirst2 + n2 * 256ULL;
          bfirst3 = (uint64_t)(uint32_t)first30;
          n4 = bfirst3 + n3 * 256ULL;
          bfirst4 = (uint64_t)(uint32_t)first20;
          n5 = bfirst4 + n4 * 256ULL;
          bfirst5 = (uint64_t)(uint32_t)first10;
          n6 = bfirst5 + n5 * 256ULL;
          bfirst6 = (uint64_t)(uint32_t)first0;
          res6 = bfirst6 + n6 * 256ULL;
          *SlPos = m0;
          tptr1 = res6;
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
            res7 = ValidateCoreT((uint32_t)17U, Ctxt, ErrorHandlerFn, base0, len0, &cursor0);
            actionSuccessTptr1 = res7 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
          resultAfterMultiProbe = resultAftertptr10;
        }
        if (resultAfterMultiProbe == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          resultAftertptr1 = resultAfterMultiProbe;
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
            startPositionMultiProbe);
          resultAftertptr1 = resultAfterMultiProbe;
        }
        if (resultAftertptr1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          p13 = *SlPos;
          fieldStartMultiProbe0 = (uint64_t)p13;
          startPositionMultiProbe0 = fieldStartMultiProbe0;
          p14 = *SlPos;
          fieldStarttptr2 = (uint64_t)p14;
          pos = (size_t)0U;
          /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
          p05 = pos;
          p = *SlPos;
          rem = SlLen - p;
          hasBytes = p05 <= rem && (size_t)8U <= (rem - p05);
          if (hasBytes)
          {
            pos = p05 + (size_t)8U;
            resultAftertptr2 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
          }
          else
          {
            resultAftertptr2 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
          }
          if (resultAftertptr2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
          {
            p0 = *SlPos;
            m = p0 + (size_t)8U;
            sub = SlBase + p0;
            pos_0 = (size_t)1U;
            first = sub[0U];
            pos_10 = pos_0 + (size_t)1U;
            first1 = sub[pos_0];
            pos_20 = pos_10 + (size_t)1U;
            first2 = sub[pos_10];
            pos_30 = pos_20 + (size_t)1U;
            first3 = sub[pos_20];
            pos_40 = pos_30 + (size_t)1U;
            first4 = sub[pos_30];
            pos_50 = pos_40 + (size_t)1U;
            first5 = sub[pos_40];
            pos_60 = pos_50 + (size_t)1U;
            first6 = sub[pos_50];
            first7 = sub[pos_60];
            n7 = (uint64_t)(uint32_t)first7;
            bfirst7 = (uint64_t)(uint32_t)first6;
            n8 = bfirst7 + n7 * 256ULL;
            bfirst8 = (uint64_t)(uint32_t)first5;
            n9 = bfirst8 + n8 * 256ULL;
            bfirst9 = (uint64_t)(uint32_t)first4;
            n10 = bfirst9 + n9 * 256ULL;
            bfirst10 = (uint64_t)(uint32_t)first3;
            n11 = bfirst10 + n10 * 256ULL;
            bfirst11 = (uint64_t)(uint32_t)first2;
            n12 = bfirst11 + n11 * 256ULL;
            bfirst12 = (uint64_t)(uint32_t)first1;
            n = bfirst12 + n12 * 256ULL;
            bfirst = (uint64_t)(uint32_t)first;
            res8 = bfirst + n * 256ULL;
            *SlPos = m;
            tptr2 = res8;
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
              res = ValidateCoreT((uint32_t)42U, Ctxt, ErrorHandlerFn, base, len, &cursor);
              actionSuccessTptr2 = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
            resultAfterMultiProbe0 =
              actionSuccessTptr2 ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                                 : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
          }
          else
          {
            resultAfterMultiProbe0 = resultAftertptr2;
          }
          if (resultAfterMultiProbe0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
          {
            return resultAfterMultiProbe0;
          }
          ErrorHandlerFn("_MultiProbe",
            "tptr2",
            EverParsePulseInternalErrorReasonOfResult(resultAfterMultiProbe0),
            resultAfterMultiProbe0 == 0U ||
              (resultAfterMultiProbe0 >= 2U && resultAfterMultiProbe0 <= 8U) ? (uint64_t)(uint32_t)resultAfterMultiProbe0
                                                                             : 15ULL,
            Ctxt,
            SlBase,
            startPositionMultiProbe0);
          return resultAfterMultiProbe0;
        }
        return resultAftertptr1;
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
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreMultiProbe(DestT1, DestT2, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreMaybeT(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos = (size_t)0U;
  size_t p1 = *SlPos;
  uint64_t viewStart = (uint64_t)p1;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterBound;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t first0;
  size_t pos_1;
  uint8_t first10;
  size_t pos_2;
  uint8_t first20;
  uint8_t first30;
  uint32_t n0;
  uint32_t bfirst0;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t res1;
  uint32_t bound;
  size_t p3;
  uint64_t fieldStartMaybeT;
  uint64_t startPositionMaybeT;
  size_t p4;
  uint64_t fieldStartptr;
  size_t pos1;
  size_t p02;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAfterptr;
  uint8_t resultAfterMaybeT;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t first;
  size_t pos_10;
  uint8_t first1;
  size_t pos_20;
  uint8_t first2;
  size_t pos_3;
  uint8_t first3;
  size_t pos_4;
  uint8_t first4;
  size_t pos_5;
  uint8_t first5;
  size_t pos_6;
  uint8_t first6;
  uint8_t first7;
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
  uint64_t n;
  uint64_t bfirst;
  uint64_t res2;
  uint64_t ptr;
  uint64_t src64;
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
  uint8_t res;
  if (hasBytes0)
  {
    pos = p00 + (size_t)4U;
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterBound = res0;
  }
  else
  {
    ErrorHandlerFn("_MaybeT",
      "Bound",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterBound = res0;
  }
  if (resultAfterBound == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)4U;
    sub0 = SlBase + p01;
    pos_ = (size_t)1U;
    first0 = sub0[0U];
    pos_1 = pos_ + (size_t)1U;
    first10 = sub0[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first20 = sub0[pos_1];
    first30 = sub0[pos_2];
    n0 = (uint32_t)first30;
    bfirst0 = (uint32_t)first20;
    n1 = bfirst0 + n0 * 256U;
    bfirst1 = (uint32_t)first10;
    n2 = bfirst1 + n1 * 256U;
    bfirst2 = (uint32_t)first0;
    res1 = bfirst2 + n2 * 256U;
    *SlPos = m0;
    bound = res1;
    p3 = *SlPos;
    fieldStartMaybeT = (uint64_t)p3;
    startPositionMaybeT = fieldStartMaybeT;
    p4 = *SlPos;
    fieldStartptr = (uint64_t)p4;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    p02 = pos1;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p02 <= rem && (size_t)8U <= (rem - p02);
    if (hasBytes)
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
      p0 = *SlPos;
      m = p0 + (size_t)8U;
      sub = SlBase + p0;
      pos_0 = (size_t)1U;
      first = sub[0U];
      pos_10 = pos_0 + (size_t)1U;
      first1 = sub[pos_0];
      pos_20 = pos_10 + (size_t)1U;
      first2 = sub[pos_10];
      pos_3 = pos_20 + (size_t)1U;
      first3 = sub[pos_20];
      pos_4 = pos_3 + (size_t)1U;
      first4 = sub[pos_3];
      pos_5 = pos_4 + (size_t)1U;
      first5 = sub[pos_4];
      pos_6 = pos_5 + (size_t)1U;
      first6 = sub[pos_5];
      first7 = sub[pos_6];
      n3 = (uint64_t)(uint32_t)first7;
      bfirst3 = (uint64_t)(uint32_t)first6;
      n4 = bfirst3 + n3 * 256ULL;
      bfirst4 = (uint64_t)(uint32_t)first5;
      n5 = bfirst4 + n4 * 256ULL;
      bfirst5 = (uint64_t)(uint32_t)first4;
      n6 = bfirst5 + n5 * 256ULL;
      bfirst6 = (uint64_t)(uint32_t)first3;
      n7 = bfirst6 + n6 * 256ULL;
      bfirst7 = (uint64_t)(uint32_t)first2;
      n8 = bfirst7 + n7 * 256ULL;
      bfirst8 = (uint64_t)(uint32_t)first1;
      n = bfirst8 + n8 * 256ULL;
      bfirst = (uint64_t)(uint32_t)first;
      res2 = bfirst + n * 256ULL;
      *SlPos = m;
      ptr = res2;
      src64 = ptr;
      if (src64 == 0ULL)
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
          base = EverParseStreamOf(Dest);
          len = (size_t)EverParseStreamLen(Dest);
          cursor = (size_t)0U;
          res = ValidateCoreT(bound, Ctxt, ErrorHandlerFn, base, len, &cursor);
          actionSuccessPtr = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
      startPositionMaybeT);
    return resultAfterMaybeT;
  }
  return resultAfterBound;
}

uint64_t
ProbeValidateMaybeT(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreMaybeT(Dest, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreCoercePtr(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t pos = (size_t)0U;
  size_t p1 = *SlPos;
  uint64_t viewStart = (uint64_t)p1;
  size_t fieldOff = pos;
  uint64_t startPos = viewStart + (uint64_t)fieldOff;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterBound;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t first0;
  size_t pos_1;
  uint8_t first10;
  size_t pos_2;
  uint8_t first20;
  uint8_t first30;
  uint32_t n0;
  uint32_t bfirst0;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t res1;
  uint32_t bound;
  size_t p3;
  uint64_t fieldStartCoercePtr;
  uint64_t startPositionCoercePtr;
  size_t p4;
  uint64_t fieldStartptr;
  size_t pos1;
  size_t p02;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAfterptr;
  uint8_t resultAfterCoercePtr;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t first;
  size_t pos_10;
  uint8_t first1;
  size_t pos_20;
  uint8_t first2;
  uint8_t first3;
  uint32_t n3;
  uint32_t bfirst3;
  uint32_t n4;
  uint32_t bfirst4;
  uint32_t n;
  uint32_t bfirst;
  uint32_t res2;
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
  uint8_t res;
  if (hasBytes0)
  {
    pos = p00 + (size_t)4U;
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterBound = res0;
  }
  else
  {
    ErrorHandlerFn("_CoercePtr",
      "Bound",
      EverParsePulseInternalErrorReasonOfResult(res0),
      res0 == 0U || (res0 >= 2U && res0 <= 8U) ? (uint64_t)(uint32_t)res0 : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterBound = res0;
  }
  if (resultAfterBound == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)4U;
    sub0 = SlBase + p01;
    pos_ = (size_t)1U;
    first0 = sub0[0U];
    pos_1 = pos_ + (size_t)1U;
    first10 = sub0[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first20 = sub0[pos_1];
    first30 = sub0[pos_2];
    n0 = (uint32_t)first30;
    bfirst0 = (uint32_t)first20;
    n1 = bfirst0 + n0 * 256U;
    bfirst1 = (uint32_t)first10;
    n2 = bfirst1 + n1 * 256U;
    bfirst2 = (uint32_t)first0;
    res1 = bfirst2 + n2 * 256U;
    *SlPos = m0;
    bound = res1;
    p3 = *SlPos;
    fieldStartCoercePtr = (uint64_t)p3;
    startPositionCoercePtr = fieldStartCoercePtr;
    p4 = *SlPos;
    fieldStartptr = (uint64_t)p4;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p02 <= rem && (size_t)4U <= (rem - p02);
    if (hasBytes)
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
      p0 = *SlPos;
      m = p0 + (size_t)4U;
      sub = SlBase + p0;
      pos_0 = (size_t)1U;
      first = sub[0U];
      pos_10 = pos_0 + (size_t)1U;
      first1 = sub[pos_0];
      pos_20 = pos_10 + (size_t)1U;
      first2 = sub[pos_10];
      first3 = sub[pos_20];
      n3 = (uint32_t)first3;
      bfirst3 = (uint32_t)first2;
      n4 = bfirst3 + n3 * 256U;
      bfirst4 = (uint32_t)first1;
      n = bfirst4 + n4 * 256U;
      bfirst = (uint32_t)first;
      res2 = bfirst + n * 256U;
      *SlPos = m;
      ptr = res2;
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
        res = ValidateCoreT(bound, Ctxt, ErrorHandlerFn, base, len, &cursor);
        actionSuccessPtr = res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
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
      startPositionCoercePtr);
    return resultAfterCoercePtr;
  }
  return resultAfterBound;
}

uint64_t
ProbeValidateCoercePtr(
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreCoercePtr(Dest, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreProbeOnly(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartProbeOnly = (uint64_t)p1;
  uint64_t startPositionProbeOnly = fieldStartProbeOnly;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterProbeOnly;
  size_t consumed;
  size_t p;
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
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
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
    startPositionProbeOnly);
  return resultAfterProbeOnly;
}

uint64_t
ProbeValidateProbeOnly(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreProbeOnly(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreBothEntrypoints(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartBothEntrypoints = (uint64_t)p1;
  uint64_t startPositionBothEntrypoints = fieldStartBothEntrypoints;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterBothEntrypoints;
  size_t consumed;
  size_t p;
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
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
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
    startPositionBothEntrypoints);
  return resultAfterBothEntrypoints;
}

uint64_t
ProbeValidateBothEntrypoints(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreBothEntrypoints(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreNamedPlainEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartNamedPlainEp = (uint64_t)p1;
  uint64_t startPositionNamedPlainEp = fieldStartNamedPlainEp;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterNamedPlainEp;
  size_t consumed;
  size_t p;
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
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
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
    startPositionNamedPlainEp);
  return resultAfterNamedPlainEp;
}

uint64_t
ProbeValidateNamedPlainEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreNamedPlainEp(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreNamedProbeEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartNamedProbeEp = (uint64_t)p1;
  uint64_t startPositionNamedProbeEp = fieldStartNamedProbeEp;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterNamedProbeEp;
  size_t consumed;
  size_t p;
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
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
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
    startPositionNamedProbeEp);
  return resultAfterNamedProbeEp;
}

uint64_t
ProbeValidateNamedProbeEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreNamedProbeEp(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

static uint8_t
ValidateCoreNamedBothEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartNamedBothEp = (uint64_t)p1;
  uint64_t startPositionNamedBothEp = fieldStartNamedBothEp;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p2 = *SlPos;
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterNamedBothEp;
  size_t consumed;
  size_t p;
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
    p = *SlPos;
    p_ = p + consumed;
    *SlPos = p_;
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
    startPositionNamedBothEp);
  return resultAfterNamedBothEp;
}

uint64_t
ProbeValidateNamedBothEp(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER Handler,
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
)
{
  size_t len = (size_t)Length;
  size_t initial = (size_t)Start;
  size_t cursor = initial;
  uint8_t status = ValidateCoreNamedBothEp(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

