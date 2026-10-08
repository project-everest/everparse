

#include "BoundedSumWhere.h"

#include "EverParse.h"

uint8_t
BoundedSumWhereValidateBoundedSum(
  uint32_t Bound,
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
  size_t p = SlPos[0U];
  uint64_t fieldStartBoundedSum = (uint64_t)p;
  /* Validating field __precondition */
  BOOLEAN preconditionConstraintIsOk = Bound <= 1729U;
  uint8_t resultAfterBoundedSum;
  size_t pos;
  size_t p1;
  uint64_t viewStart;
  size_t fieldOff;
  uint64_t startPos;
  size_t p0;
  size_t p2;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res;
  uint8_t resultAfterleft;
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
  uint32_t left;
  size_t p3;
  uint64_t fieldStartBoundedSum1;
  size_t pos1;
  size_t p02;
  size_t p4;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterright_refinement;
  uint8_t resultAfterBoundedSum0;
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
  uint32_t right_refinement;
  BOOLEAN right_refinementConstraintIsOk;
  if (preconditionConstraintIsOk)
  {
    pos = (size_t)0U;
    p1 = SlPos[0U];
    viewStart = (uint64_t)p1;
    fieldOff = pos;
    startPos = viewStart + (uint64_t)fieldOff;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p0 = pos;
    p2 = SlPos[0U];
    rem = SlLen - p2;
    hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
    if (hasBytes)
    {
      pos = p0 + (size_t)4U;
      res = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res == EVERPARSE_VALIDATOR_SUCCESS)
    {
      resultAfterleft = res;
    }
    else
    {
      ErrorHandlerFn("_boundedSum",
        "left",
        EverParseErrorReasonOfResult(res),
        res,
        Ctxt,
        SlBase,
        SlLen,
        SlPos,
        startPos);
      resultAfterleft = res;
    }
    if (resultAfterleft == EVERPARSE_VALIDATOR_SUCCESS)
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
      left = bfirst2 + n2 * 256U;
      /* Validating field right */
      p3 = SlPos[0U];
      fieldStartBoundedSum1 = (uint64_t)p3;
      pos1 = (size_t)0U;
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      p02 = pos1;
      p4 = SlPos[0U];
      rem1 = SlLen - p4;
      hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
      if (hasBytes1)
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
        right_refinement = bfirst5 + n5 * 256U;
        /* start: checking constraint */
        right_refinementConstraintIsOk = left <= Bound && right_refinement <= (Bound - left);
        /* end: checking constraint */
        resultAfterBoundedSum0 =
          right_refinementConstraintIsOk ? EVERPARSE_VALIDATOR_SUCCESS
                                         : EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
      else
      {
        resultAfterBoundedSum0 = resultAfterright_refinement;
      }
      if (resultAfterBoundedSum0 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        resultAfterBoundedSum = resultAfterBoundedSum0;
      }
      else
      {
        ErrorHandlerFn("_boundedSum",
          "right.refinement",
          EverParseErrorReasonOfResult(resultAfterBoundedSum0),
          resultAfterBoundedSum0,
          Ctxt,
          SlBase,
          SlLen,
          SlPos,
          fieldStartBoundedSum1);
        resultAfterBoundedSum = resultAfterBoundedSum0;
      }
    }
    else
    {
      resultAfterBoundedSum = resultAfterleft;
    }
  }
  else
  {
    resultAfterBoundedSum = EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
  }
  if (resultAfterBoundedSum == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterBoundedSum;
  }
  ErrorHandlerFn("_boundedSum",
    "__precondition",
    EverParseErrorReasonOfResult(resultAfterBoundedSum),
    resultAfterBoundedSum,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartBoundedSum);
  return resultAfterBoundedSum;
}

