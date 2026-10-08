

#include "ReadPair.h"

#include "EverParse.h"

uint8_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
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
  /* Validating field first */
  size_t p = SlPos[0U];
  uint64_t fieldStartPair = (uint64_t)p;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p2 = SlPos[0U];
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t resultAfterfirst;
  uint8_t resultAfterPair;
  size_t p010;
  size_t m0;
  uint8_t *sub0;
  uint8_t first0;
  size_t pos_;
  uint8_t first10;
  size_t pos_1;
  uint8_t first20;
  uint8_t first30;
  uint32_t n0;
  uint32_t bfirst0;
  uint32_t n10;
  uint32_t bfirst10;
  uint32_t n20;
  uint32_t bfirst20;
  uint32_t first4;
  uint8_t resultAfterfirst1;
  size_t p3;
  uint64_t fieldStartPair1;
  size_t pos1;
  size_t p01;
  size_t p5;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAftersecond;
  uint8_t resultAfterPair1;
  size_t p02;
  size_t m;
  uint8_t *sub;
  uint8_t first;
  size_t pos_0;
  uint8_t first1;
  size_t pos_10;
  uint8_t first2;
  uint8_t first3;
  uint32_t n;
  uint32_t bfirst;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n2;
  uint32_t bfirst2;
  uint32_t second;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    resultAfterfirst = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterfirst = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterfirst == EVERPARSE_VALIDATOR_SUCCESS)
  {
    p010 = SlPos[0U];
    m0 = p010 + (size_t)4U;
    sub0 = SlBase + p010;
    SlPos[0U] = m0;
    first0 = sub0[0U];
    pos_ = (size_t)2U;
    first10 = sub0[1U];
    pos_1 = pos_ + (size_t)1U;
    first20 = sub0[pos_];
    first30 = sub0[pos_1];
    n0 = (uint32_t)first30;
    bfirst0 = (uint32_t)first20;
    n10 = bfirst0 + n0 * 256U;
    bfirst10 = (uint32_t)first10;
    n20 = bfirst10 + n10 * 256U;
    bfirst20 = (uint32_t)first0;
    first4 = bfirst20 + n20 * 256U;
    X[0U] = first4;
    resultAfterPair = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterPair = resultAfterfirst;
  }
  if (resultAfterPair == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterfirst1 = resultAfterPair;
  }
  else
  {
    ErrorHandlerFn("_Pair",
      "first",
      EverParseErrorReasonOfResult(resultAfterPair),
      resultAfterPair,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartPair);
    resultAfterfirst1 = resultAfterPair;
  }
  if (resultAfterfirst1 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    /* Validating field second */
    p3 = SlPos[0U];
    fieldStartPair1 = (uint64_t)p3;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p01 = pos1;
    p5 = SlPos[0U];
    rem1 = SlLen - p5;
    hasBytes1 = p01 <= rem1 && (size_t)4U <= (rem1 - p01);
    if (hasBytes1)
    {
      pos1 = p01 + (size_t)4U;
      resultAftersecond = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftersecond = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftersecond == EVERPARSE_VALIDATOR_SUCCESS)
    {
      p02 = SlPos[0U];
      m = p02 + (size_t)4U;
      sub = SlBase + p02;
      SlPos[0U] = m;
      first = sub[0U];
      pos_0 = (size_t)2U;
      first1 = sub[1U];
      pos_10 = pos_0 + (size_t)1U;
      first2 = sub[pos_0];
      first3 = sub[pos_10];
      n = (uint32_t)first3;
      bfirst = (uint32_t)first2;
      n1 = bfirst + n * 256U;
      bfirst1 = (uint32_t)first1;
      n2 = bfirst1 + n1 * 256U;
      bfirst2 = (uint32_t)first;
      second = bfirst2 + n2 * 256U;
      Y[0U] = second;
      resultAfterPair1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterPair1 = resultAftersecond;
    }
    if (resultAfterPair1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterPair1;
    }
    ErrorHandlerFn("_Pair",
      "second",
      EverParseErrorReasonOfResult(resultAfterPair1),
      resultAfterPair1,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartPair1);
    return resultAfterPair1;
  }
  return resultAfterfirst1;
}

