

#include "BF.h"

#include "EverParse.h"

static inline uint8_t
ValidateBf2bis(
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
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)2U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterBitfield0;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t first0;
  uint8_t first10;
  uint16_t n0;
  uint16_t bfirst0;
  uint16_t res1;
  uint16_t bitfield0;
  size_t p3;
  uint64_t fieldStartBf2bis;
  uint64_t startPositionBf2bis;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterBitfield1;
  uint8_t resultAfterBf2bis;
  size_t p03;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t first;
  uint8_t first1;
  uint16_t n;
  uint16_t bfirst;
  uint16_t res2;
  uint16_t bitfield1;
  BOOLEAN bitfield1constraintIsOk;
  size_t pos2;
  size_t p5;
  uint64_t viewStart0;
  size_t fieldOff0;
  uint64_t startPos0;
  size_t p0;
  size_t p6;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res3;
  uint8_t res;
  size_t consumed;
  size_t p;
  size_t p_;
  if (hasBytes0)
  {
    pos = p00 + (size_t)2U;
    res0 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterBitfield0 = res0;
  }
  else
  {
    ErrorHandlerFn("_BF2bis",
      "__bitfield_0",
      EverParseErrorReasonOfResult(res0),
      res0,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    resultAfterBitfield0 = res0;
  }
  if (resultAfterBitfield0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)2U;
    sub0 = SlBase + p01;
    pos_ = (size_t)1U;
    first0 = sub0[0U];
    first10 = sub0[pos_];
    n0 = (uint16_t)(uint32_t)first10;
    bfirst0 = (uint16_t)(uint32_t)first0;
    res1 = (uint32_t)bfirst0 + (uint32_t)n0 * 256U;
    *SlPos = m0;
    bitfield0 = res1;
    p3 = *SlPos;
    fieldStartBf2bis = (uint64_t)p3;
    startPositionBf2bis = fieldStartBf2bis;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    p02 = pos1;
    p4 = *SlPos;
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)2U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)2U;
      resultAfterBitfield1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterBitfield1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterBitfield1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      p03 = *SlPos;
      m = p03 + (size_t)2U;
      sub = SlBase + p03;
      pos_0 = (size_t)1U;
      first = sub[0U];
      first1 = sub[pos_0];
      n = (uint16_t)(uint32_t)first1;
      bfirst = (uint16_t)(uint32_t)first;
      res2 = (uint32_t)bfirst + (uint32_t)n * 256U;
      *SlPos = m;
      bitfield1 = res2;
      bitfield1constraintIsOk =
        EverParseGetBitfield16(bitfield1, 0U, 12U) < EverParseGetBitfield16(bitfield0, 0U, 6U);
      if (bitfield1constraintIsOk)
      {
        pos2 = (size_t)0U;
        /* Validating field z */
        p5 = *SlPos;
        viewStart0 = (uint64_t)p5;
        fieldOff0 = pos2;
        startPos0 = viewStart0 + (uint64_t)fieldOff0;
        /* Checking that we have enough space for a UINT8, i.e., 1 byte */
        p0 = pos2;
        p6 = *SlPos;
        rem = SlLen - p6;
        hasBytes = p0 <= rem && (size_t)1U <= (rem - p0);
        if (hasBytes)
        {
          pos2 = p0 + (size_t)1U;
          res3 = EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          res3 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (res3 == EVERPARSE_VALIDATOR_SUCCESS)
        {
          res = res3;
        }
        else
        {
          ErrorHandlerFn("_BF2bis",
            "z",
            EverParseErrorReasonOfResult(res3),
            res3,
            Ctxt,
            SlBase,
            SlLen,
            SlPos,
            startPos0);
          res = res3;
        }
        if (res == EVERPARSE_VALIDATOR_SUCCESS)
        {
          consumed = pos2;
          p = *SlPos;
          p_ = p + consumed;
          *SlPos = p_;
          resultAfterBf2bis = EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAfterBf2bis = res;
        }
      }
      else
      {
        resultAfterBf2bis = EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
    }
    else
    {
      resultAfterBf2bis = resultAfterBitfield1;
    }
    if (resultAfterBf2bis == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterBf2bis;
    }
    ErrorHandlerFn("_BF2bis",
      "__bitfield_1",
      EverParseErrorReasonOfResult(resultAfterBf2bis),
      resultAfterBf2bis,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionBf2bis);
    return resultAfterBf2bis;
  }
  return resultAfterBitfield0;
}

static inline uint8_t
ValidateBf3(
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
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)2U <= (rem0 - p00);
  uint8_t res0;
  uint8_t resultAfterBitfield0;
  size_t p01;
  size_t m0;
  uint8_t *sub0;
  size_t pos_;
  uint8_t last0;
  uint8_t last10;
  uint16_t n0;
  uint16_t blast0;
  uint16_t res1;
  uint16_t bitfield0;
  size_t p3;
  uint64_t fieldStartBf3;
  uint64_t startPositionBf3;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterBitfield1;
  uint8_t resultAfterBf3;
  size_t p03;
  size_t m;
  uint8_t *sub;
  size_t pos_0;
  uint8_t last;
  uint8_t last1;
  uint16_t n;
  uint16_t blast;
  uint16_t res2;
  uint16_t bitfield1;
  BOOLEAN bitfield1constraintIsOk;
  size_t pos2;
  size_t p5;
  uint64_t viewStart0;
  size_t fieldOff0;
  uint64_t startPos0;
  size_t p0;
  size_t p6;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res3;
  uint8_t res;
  size_t consumed;
  size_t p;
  size_t p_;
  if (hasBytes0)
  {
    pos = p00 + (size_t)2U;
    res0 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterBitfield0 = res0;
  }
  else
  {
    ErrorHandlerFn("_BF3",
      "__bitfield_0",
      EverParseErrorReasonOfResult(res0),
      res0,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    resultAfterBitfield0 = res0;
  }
  if (resultAfterBitfield0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m0 = p01 + (size_t)2U;
    sub0 = SlBase + p01;
    pos_ = (size_t)1U;
    last0 = sub0[pos_];
    last10 = sub0[0U];
    n0 = (uint16_t)(uint32_t)last10;
    blast0 = (uint16_t)(uint32_t)last0;
    res1 = (uint32_t)blast0 + (uint32_t)n0 * 256U;
    *SlPos = m0;
    bitfield0 = res1;
    p3 = *SlPos;
    fieldStartBf3 = (uint64_t)p3;
    startPositionBf3 = fieldStartBf3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
    p02 = pos1;
    p4 = *SlPos;
    rem1 = SlLen - p4;
    hasBytes1 = p02 <= rem1 && (size_t)2U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)2U;
      resultAfterBitfield1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterBitfield1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterBitfield1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      p03 = *SlPos;
      m = p03 + (size_t)2U;
      sub = SlBase + p03;
      pos_0 = (size_t)1U;
      last = sub[pos_0];
      last1 = sub[0U];
      n = (uint16_t)(uint32_t)last1;
      blast = (uint16_t)(uint32_t)last;
      res2 = (uint32_t)blast + (uint32_t)n * 256U;
      *SlPos = m;
      bitfield1 = res2;
      bitfield1constraintIsOk =
        EverParseGetBitfield16MsbFirst(bitfield1, 0U, 12U) <
          EverParseGetBitfield16MsbFirst(bitfield0,
            0U,
            6U);
      if (bitfield1constraintIsOk)
      {
        pos2 = (size_t)0U;
        /* Validating field z */
        p5 = *SlPos;
        viewStart0 = (uint64_t)p5;
        fieldOff0 = pos2;
        startPos0 = viewStart0 + (uint64_t)fieldOff0;
        /* Checking that we have enough space for a UINT8BE, i.e., 1 byte */
        p0 = pos2;
        p6 = *SlPos;
        rem = SlLen - p6;
        hasBytes = p0 <= rem && (size_t)1U <= (rem - p0);
        if (hasBytes)
        {
          pos2 = p0 + (size_t)1U;
          res3 = EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          res3 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
        }
        if (res3 == EVERPARSE_VALIDATOR_SUCCESS)
        {
          res = res3;
        }
        else
        {
          ErrorHandlerFn("_BF3",
            "z",
            EverParseErrorReasonOfResult(res3),
            res3,
            Ctxt,
            SlBase,
            SlLen,
            SlPos,
            startPos0);
          res = res3;
        }
        if (res == EVERPARSE_VALIDATOR_SUCCESS)
        {
          consumed = pos2;
          p = *SlPos;
          p_ = p + consumed;
          *SlPos = p_;
          resultAfterBf3 = EVERPARSE_VALIDATOR_SUCCESS;
        }
        else
        {
          resultAfterBf3 = res;
        }
      }
      else
      {
        resultAfterBf3 = EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
    }
    else
    {
      resultAfterBf3 = resultAfterBitfield1;
    }
    if (resultAfterBf3 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterBf3;
    }
    ErrorHandlerFn("_BF3",
      "__bitfield_1",
      EverParseErrorReasonOfResult(resultAfterBf3),
      resultAfterBf3,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionBf3);
    return resultAfterBf3;
  }
  return resultAfterBitfield0;
}

uint8_t
BfValidateDummy(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field emp2 */
  size_t p0 = *SlPos;
  uint64_t fieldStartDummy = (uint64_t)p0;
  uint64_t startPositionDummy = fieldStartDummy;
  uint8_t resultAfterDummy = ValidateBf2bis(Ctxt, ErrorHandlerFn, SlBase, SlLen, SlPos);
  uint8_t resultAfteremp2;
  size_t p;
  uint64_t fieldStartDummy0;
  uint64_t startPositionDummy0;
  uint8_t resultAfterDummy0;
  if (resultAfterDummy == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfteremp2 = resultAfterDummy;
  }
  else
  {
    ErrorHandlerFn("_dummy",
      "emp2",
      EverParseErrorReasonOfResult(resultAfterDummy),
      resultAfterDummy,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionDummy);
    resultAfteremp2 = resultAfterDummy;
  }
  if (resultAfteremp2 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    /* Validating field emp3 */
    p = *SlPos;
    fieldStartDummy0 = (uint64_t)p;
    startPositionDummy0 = fieldStartDummy0;
    resultAfterDummy0 = ValidateBf3(Ctxt, ErrorHandlerFn, SlBase, SlLen, SlPos);
    if (resultAfterDummy0 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterDummy0;
    }
    ErrorHandlerFn("_dummy",
      "emp3",
      EverParseErrorReasonOfResult(resultAfterDummy0),
      resultAfterDummy0,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionDummy0);
    return resultAfterDummy0;
  }
  return resultAfteremp2;
}

