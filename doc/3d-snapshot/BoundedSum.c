

#include "BoundedSum.h"

#include "EverParse.h"

uint8_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
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
  uint8_t resultAfterleft;
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
  uint32_t left;
  size_t p3;
  uint64_t fieldStartBoundedSum;
  uint64_t startPositionBoundedSum;
  size_t pos1;
  size_t p02;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAfterright_refinement;
  uint8_t resultAfterBoundedSum;
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
  uint32_t res;
  uint32_t right_refinement;
  BOOLEAN right_refinementConstraintIsOk;
  if (hasBytes0)
  {
    pos = p00 + (size_t)4U;
    res0 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterleft = res0;
  }
  else
  {
    ErrorHandlerFn("_boundedSum",
      "left",
      EverParseErrorReasonOfResult(res0),
      res0,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    resultAfterleft = res0;
  }
  if (resultAfterleft == EVERPARSE_VALIDATOR_SUCCESS)
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
    left = res1;
    /* Validating field right */
    p3 = *SlPos;
    fieldStartBoundedSum = (uint64_t)p3;
    startPositionBoundedSum = fieldStartBoundedSum;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p02 <= rem && (size_t)4U <= (rem - p02);
    if (hasBytes)
    {
      pos1 = p02 + (size_t)4U;
      resultAfterright_refinement = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterright_refinement = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterright_refinement == EVERPARSE_VALIDATOR_SUCCESS)
    {
      /* reading field_value */
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
      res = bfirst + n * 256U;
      *SlPos = m;
      right_refinement = res;
      /* start: checking constraint */
      right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
      /* end: checking constraint */
      resultAfterBoundedSum =
        right_refinementConstraintIsOk ? EVERPARSE_VALIDATOR_SUCCESS
                                       : EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
    else
    {
      resultAfterBoundedSum = resultAfterright_refinement;
    }
    if (resultAfterBoundedSum == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterBoundedSum;
    }
    ErrorHandlerFn("_boundedSum",
      "right.refinement",
      EverParseErrorReasonOfResult(resultAfterBoundedSum),
      resultAfterBoundedSum,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionBoundedSum);
    return resultAfterBoundedSum;
  }
  return resultAfterleft;
}

uint8_t
BoundedSumValidateMySum(
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
  size_t rem = SlLen - p2;
  BOOLEAN hasBytes = p00 <= rem && (size_t)4U <= (rem - p00);
  uint8_t res0;
  uint8_t resultAfterbound;
  size_t p0;
  size_t m;
  uint8_t *sub;
  size_t pos_;
  uint8_t first;
  size_t pos_1;
  uint8_t first1;
  size_t pos_2;
  uint8_t first2;
  uint8_t first3;
  uint32_t n0;
  uint32_t bfirst0;
  uint32_t n1;
  uint32_t bfirst1;
  uint32_t n;
  uint32_t bfirst;
  uint32_t res;
  uint32_t bound;
  size_t p;
  uint64_t fieldStartmySum;
  uint64_t startPositionmySum;
  uint8_t resultAftermySum;
  if (hasBytes)
  {
    pos = p00 + (size_t)4U;
    res0 = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    res0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res0 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAfterbound = res0;
  }
  else
  {
    ErrorHandlerFn("mySum",
      "bound",
      EverParseErrorReasonOfResult(res0),
      res0,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    resultAfterbound = res0;
  }
  if (resultAfterbound == EVERPARSE_VALIDATOR_SUCCESS)
  {
    p0 = *SlPos;
    m = p0 + (size_t)4U;
    sub = SlBase + p0;
    pos_ = (size_t)1U;
    first = sub[0U];
    pos_1 = pos_ + (size_t)1U;
    first1 = sub[pos_];
    pos_2 = pos_1 + (size_t)1U;
    first2 = sub[pos_1];
    first3 = sub[pos_2];
    n0 = (uint32_t)first3;
    bfirst0 = (uint32_t)first2;
    n1 = bfirst0 + n0 * 256U;
    bfirst1 = (uint32_t)first1;
    n = bfirst1 + n1 * 256U;
    bfirst = (uint32_t)first;
    res = bfirst + n * 256U;
    *SlPos = m;
    bound = res;
    /* Validating field sum */
    p = *SlPos;
    fieldStartmySum = (uint64_t)p;
    startPositionmySum = fieldStartmySum;
    resultAftermySum =
      BoundedSumValidateBoundedSum(bound,
        Ctxt,
        ErrorHandlerFn,
        SlBase,
        SlLen,
        SlPos);
    if (resultAftermySum == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAftermySum;
    }
    ErrorHandlerFn("mySum",
      "sum",
      EverParseErrorReasonOfResult(resultAftermySum),
      resultAftermySum,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPositionmySum);
    return resultAftermySum;
  }
  return resultAfterbound;
}

