

#include "OrderedPair.h"

#include "EverParse.h"

uint8_t
OrderedPairValidateOrderedPair(
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
  uint8_t resultAfterlesser;
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
  uint32_t lesser;
  size_t p2;
  uint64_t fieldStartOrderedPair;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAftergreater_refinement;
  uint8_t resultAfterOrderedPair;
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
  uint32_t greater_refinement;
  BOOLEAN greater_refinementConstraintIsOk;
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
    resultAfterlesser = res;
  }
  else
  {
    ErrorHandlerFn("_orderedPair",
      "lesser",
      EverParseErrorReasonOfResult(res),
      res,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      startPos);
    resultAfterlesser = res;
  }
  if (resultAfterlesser == EVERPARSE_VALIDATOR_SUCCESS)
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
    lesser = bfirst2 + n2 * 256U;
    /* Validating field greater */
    p2 = SlPos[0U];
    fieldStartOrderedPair = (uint64_t)p2;
    pos1 = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
    if (hasBytes1)
    {
      pos1 = p02 + (size_t)4U;
      resultAftergreater_refinement = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftergreater_refinement = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftergreater_refinement == EVERPARSE_VALIDATOR_SUCCESS)
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
      greater_refinement = bfirst5 + n5 * 256U;
      /* start: checking constraint */
      greater_refinementConstraintIsOk = lesser <= greater_refinement;
      /* end: checking constraint */
      resultAfterOrderedPair =
        greater_refinementConstraintIsOk ? EVERPARSE_VALIDATOR_SUCCESS
                                         : EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
    else
    {
      resultAfterOrderedPair = resultAftergreater_refinement;
    }
    if (resultAfterOrderedPair == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterOrderedPair;
    }
    ErrorHandlerFn("_orderedPair",
      "greater.refinement",
      EverParseErrorReasonOfResult(resultAfterOrderedPair),
      resultAfterOrderedPair,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartOrderedPair);
    return resultAfterOrderedPair;
  }
  return resultAfterlesser;
}

