

#include "BoundedSumConst.h"

uint8_t
BoundedSumConstValidateCoreBoundedSum(
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
  size_t p2;
  uint64_t fieldStartBoundedSum;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterright_refinement;
  uint8_t resultAfterBoundedSum;
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
    resultAfterleft = res;
  }
  else
  {
    ErrorHandlerFn("_boundedSum",
      "left",
      EverParsePulseInternalErrorReasonOfResult(res),
      res == 0U || (res >= 2U && res <= 8U) ? (uint64_t)(uint32_t)res : 15ULL,
      Ctxt,
      SlBase,
      startPos);
    resultAfterleft = res;
  }
  if (resultAfterleft == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
    p2 = SlPos[0U];
    fieldStartBoundedSum = (uint64_t)p2;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)4U;
      resultAfterright_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterright_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAfterright_refinement == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
      right_refinementConstraintIsOk = left <= 42U && right_refinement <= ((uint32_t)42U - left);
      /* end: checking constraint */
      resultAfterBoundedSum =
        right_refinementConstraintIsOk ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                                       : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
    else
    {
      resultAfterBoundedSum = resultAfterright_refinement;
    }
    if (resultAfterBoundedSum == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterBoundedSum;
    }
    ErrorHandlerFn("_boundedSum",
      "right.refinement",
      EverParsePulseInternalErrorReasonOfResult(resultAfterBoundedSum),
      resultAfterBoundedSum == 0U || (resultAfterBoundedSum >= 2U && resultAfterBoundedSum <= 8U) ? (uint64_t)(uint32_t)resultAfterBoundedSum
                                                                                                  : 15ULL,
      Ctxt,
      SlBase,
      fieldStartBoundedSum);
    return resultAfterBoundedSum;
  }
  return resultAfterleft;
}

uint64_t
BoundedSumConstValidateBoundedSum(
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
  uint8_t status = BoundedSumConstValidateCoreBoundedSum(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

