

#include "BF.h"

inline uint8_t
BfValidateCoreBf2bis(
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
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)2U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterBitfield0;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  uint8_t first1;
  uint16_t n;
  uint16_t bfirst;
  uint16_t bitfield0;
  size_t p2;
  uint64_t fieldStartBf2bis;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterBitfield1;
  uint8_t resultAfterBf2bis;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  uint8_t first2;
  uint8_t first3;
  uint16_t n1;
  uint16_t bfirst1;
  uint16_t bitfield1;
  BOOLEAN bitfield1constraintIsOk;
  size_t pos2;
  size_t p4;
  uint64_t viewStart1;
  size_t fieldOff1;
  uint64_t startPos1;
  size_t p04;
  size_t p5;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t res1;
  uint8_t res2;
  size_t consumed;
  size_t p6;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)2U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterBitfield0 = res;
  }
  else
  {
    ErrorHandlerFn("_BF2bis",
      "__bitfield_0",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterBitfield0 = res;
  }
  if (resultAfterBitfield0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)2U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    first = sub[0U];
    first1 = sub[1U];
    n = (uint16_t)(uint32_t)first1;
    bfirst = (uint16_t)(uint32_t)first;
    bitfield0 = (uint32_t)bfirst + (uint32_t)n * 256U;
    p2 = SlPos[0U];
    fieldStartBf2bis = (uint64_t)p2;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    p02 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p02 <= rem1 && (size_t)2U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)2U;
      resultAfterBitfield1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterBitfield1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterBitfield1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p03 = SlPos[0U];
      m1 = p03 + (size_t)2U;
      sub1 = SlBase + p03;
      SlPos[0U] = m1;
      first2 = sub1[0U];
      first3 = sub1[1U];
      n1 = (uint16_t)(uint32_t)first3;
      bfirst1 = (uint16_t)(uint32_t)first2;
      bitfield1 = (uint32_t)bfirst1 + (uint32_t)n1 * 256U;
      bitfield1constraintIsOk =
        EverParseGetBitfield16(bitfield1, 0U, 12U) < EverParseGetBitfield16(bitfield0, 0U, 6U);
      if (bitfield1constraintIsOk)
      {
        pos2 = (size_t)0U;
        /* Validating field z */
        p4 = SlPos[0U];
        viewStart1 = (uint64_t)p4;
        fieldOff1 = pos2;
        startPos1 = viewStart1 + (uint64_t)fieldOff1;
        /* Checking that we have enough space for a UINT8, i.e., 1 byte */
        p04 = pos2;
        p5 = SlPos[0U];
        rem2 = SlLen - p5;
        hasBytes2 = p04 <= rem2 && (size_t)1U <= (rem2 - p04);
        if (hasBytes2)
        {
          pos2 = p04 + (size_t)1U;
          res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          res2 = res1;
        }
        else
        {
          ErrorHandlerFn("_BF2bis",
            "z",
            EverParsePulseInternalErrorReasonOfResult(res1),
            res1 == 0U || (res1 >= 2U && res1 <= 8U) ? (uint64_t)(uint32_t)res1 : 15ULL,
            Ctxt,
            SlBase,
            startPos1);
          res2 = res1;
        }
        if (res2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          consumed = pos2;
          p6 = SlPos[0U];
          p_ = p6 + consumed;
          SlPos[0U] = p_;
          resultAfterBf2bis = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAfterBf2bis = res2;
        }
      }
      else
      {
        resultAfterBf2bis = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
    }
    else
    {
      resultAfterBf2bis = resultAfterBitfield1;
    }
    if (resultAfterBf2bis == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterBf2bis;
    }
    ErrorHandlerFn("_BF2bis",
      "__bitfield_1",
      EverParsePulseInternalErrorReasonOfResult(resultAfterBf2bis),
      resultAfterBf2bis == 0U || (resultAfterBf2bis >= 2U && resultAfterBf2bis <= 8U) ? (uint64_t)(uint32_t)resultAfterBf2bis
                                                                                      : 15ULL,
      Ctxt,
      SlBase,
      fieldStartBf2bis);
    return resultAfterBf2bis;
  }
  return resultAfterBitfield0;
}

inline uint8_t
BfValidateCoreBf3(
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
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)2U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterBitfield0;
  size_t p01;
  size_t m;
  uint8_t *sub;
  uint8_t last;
  uint8_t last1;
  uint16_t n;
  uint16_t blast;
  uint16_t bitfield0;
  size_t p2;
  uint64_t fieldStartBf3;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterBitfield1;
  uint8_t resultAfterBf3;
  size_t p03;
  size_t m1;
  uint8_t *sub1;
  uint8_t last2;
  uint8_t last3;
  uint16_t n1;
  uint16_t blast1;
  uint16_t bitfield1;
  BOOLEAN bitfield1constraintIsOk;
  size_t pos2;
  size_t p4;
  uint64_t viewStart1;
  size_t fieldOff1;
  uint64_t startPos1;
  size_t p04;
  size_t p5;
  size_t rem2;
  BOOLEAN hasBytes2;
  uint8_t res1;
  uint8_t res2;
  size_t consumed;
  size_t p6;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)2U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterBitfield0 = res;
  }
  else
  {
    ErrorHandlerFn("_BF3",
      "__bitfield_0",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterBitfield0 = res;
  }
  if (resultAfterBitfield0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p01 = SlPos[0U];
    m = p01 + (size_t)2U;
    sub = SlBase + p01;
    SlPos[0U] = m;
    last = sub[1U];
    last1 = sub[0U];
    n = (uint16_t)(uint32_t)last1;
    blast = (uint16_t)(uint32_t)last;
    bitfield0 = (uint32_t)blast + (uint32_t)n * 256U;
    p2 = SlPos[0U];
    fieldStartBf3 = (uint64_t)p2;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
    p02 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p02 <= rem1 && (size_t)2U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)2U;
      resultAfterBitfield1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterBitfield1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterBitfield1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      p03 = SlPos[0U];
      m1 = p03 + (size_t)2U;
      sub1 = SlBase + p03;
      SlPos[0U] = m1;
      last2 = sub1[1U];
      last3 = sub1[0U];
      n1 = (uint16_t)(uint32_t)last3;
      blast1 = (uint16_t)(uint32_t)last2;
      bitfield1 = (uint32_t)blast1 + (uint32_t)n1 * 256U;
      bitfield1constraintIsOk =
        EverParseGetBitfield16MsbFirst(bitfield1, 0U, 12U) <
          EverParseGetBitfield16MsbFirst(bitfield0,
            0U,
            6U);
      if (bitfield1constraintIsOk)
      {
        pos2 = (size_t)0U;
        /* Validating field z */
        p4 = SlPos[0U];
        viewStart1 = (uint64_t)p4;
        fieldOff1 = pos2;
        startPos1 = viewStart1 + (uint64_t)fieldOff1;
        /* Checking that we have enough space for a UINT8BE, i.e., 1 byte */
        p04 = pos2;
        p5 = SlPos[0U];
        rem2 = SlLen - p5;
        hasBytes2 = p04 <= rem2 && (size_t)1U <= (rem2 - p04);
        if (hasBytes2)
        {
          pos2 = p04 + (size_t)1U;
          res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          res1 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (res1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          res2 = res1;
        }
        else
        {
          ErrorHandlerFn("_BF3",
            "z",
            EverParsePulseInternalErrorReasonOfResult(res1),
            res1 == 0U || (res1 >= 2U && res1 <= 8U) ? (uint64_t)(uint32_t)res1 : 15ULL,
            Ctxt,
            SlBase,
            startPos1);
          res2 = res1;
        }
        if (res2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
        {
          consumed = pos2;
          p6 = SlPos[0U];
          p_ = p6 + consumed;
          SlPos[0U] = p_;
          resultAfterBf3 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAfterBf3 = res2;
        }
      }
      else
      {
        resultAfterBf3 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
    }
    else
    {
      resultAfterBf3 = resultAfterBitfield1;
    }
    if (resultAfterBf3 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterBf3;
    }
    ErrorHandlerFn("_BF3",
      "__bitfield_1",
      EverParsePulseInternalErrorReasonOfResult(resultAfterBf3),
      resultAfterBf3 == 0U || (resultAfterBf3 >= 2U && resultAfterBf3 <= 8U) ? (uint64_t)(uint32_t)resultAfterBf3
                                                                             : 15ULL,
      Ctxt,
      SlBase,
      fieldStartBf3);
    return resultAfterBf3;
  }
  return resultAfterBitfield0;
}

uint8_t
BfValidateCoreDummy(
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
  /* Validating field emp2 */
  size_t p = SlPos[0U];
  uint64_t fieldStartDummy = (uint64_t)p;
  uint8_t resultAfterDummy = BfValidateCoreBf2bis(Ctxt, ErrorHandlerFn, SlBase, SlLen, SlPos);
  uint8_t resultAfteremp2;
  size_t p1;
  uint64_t fieldStartDummy1;
  uint8_t resultAfterDummy1;
  if (resultAfterDummy == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfteremp2 = resultAfterDummy;
  }
  else
  {
    ErrorHandlerFn("_dummy",
      "emp2",
      EverParsePulseInternalErrorReasonOfResult(resultAfterDummy),
      resultAfterDummy == 0U || (resultAfterDummy >= 2U && resultAfterDummy <= 8U) ? (uint64_t)(uint32_t)resultAfterDummy
                                                                                   : 15ULL,
      Ctxt,
      SlBase,
      fieldStartDummy);
    resultAfteremp2 = resultAfterDummy;
  }
  if (resultAfteremp2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    /* Validating field emp3 */
    p1 = SlPos[0U];
    fieldStartDummy1 = (uint64_t)p1;
    resultAfterDummy1 = BfValidateCoreBf3(Ctxt, ErrorHandlerFn, SlBase, SlLen, SlPos);
    if (resultAfterDummy1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterDummy1;
    }
    ErrorHandlerFn("_dummy",
      "emp3",
      EverParsePulseInternalErrorReasonOfResult(resultAfterDummy1),
      resultAfterDummy1 == 0U || (resultAfterDummy1 >= 2U && resultAfterDummy1 <= 8U) ? (uint64_t)(uint32_t)resultAfterDummy1
                                                                                      : 15ULL,
      Ctxt,
      SlBase,
      fieldStartDummy1);
    return resultAfterDummy1;
  }
  return resultAfteremp2;
}

uint64_t
BfValidateDummy(
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
  uint8_t status = BfValidateCoreDummy(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

