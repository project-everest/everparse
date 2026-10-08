

#include "Smoker.h"

#include "EverParse.h"

uint8_t
SmokerValidateSmoker(
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
  uint64_t fieldStartSmoker = (uint64_t)p;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t resultAfterage;
  uint8_t resultAfterSmoker;
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
  uint32_t age;
  BOOLEAN ageConstraintIsOk;
  size_t pos1;
  size_t p2;
  uint64_t viewStart;
  size_t fieldOff;
  uint64_t startPos;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res;
  uint8_t res1;
  size_t consumed;
  size_t p4;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    resultAfterage = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterage = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterage == EVERPARSE_VALIDATOR_SUCCESS)
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
    age = bfirst2 + n2 * 256U;
    ageConstraintIsOk = age >= 21U;
    if (ageConstraintIsOk)
    {
      pos1 = (size_t)0U;
      /* Validating field cigarettesConsumed */
      p2 = SlPos[0U];
      viewStart = (uint64_t)p2;
      fieldOff = pos1;
      startPos = viewStart + (uint64_t)fieldOff;
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      p02 = pos1;
      p3 = SlPos[0U];
      rem1 = SlLen - p3;
      hasBytes1 = p02 <= rem1 && (size_t)1U <= (rem1 - p02);
      if (hasBytes1)
      {
        pos1 = p02 + (size_t)1U;
        res = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (res == EVERPARSE_VALIDATOR_SUCCESS)
      {
        res1 = res;
      }
      else
      {
        ErrorHandlerFn("_smoker",
          "cigarettesConsumed",
          EverParseErrorReasonOfResult(res),
          res,
          Ctxt,
          SlBase,
          SlLen,
          SlPos,
          startPos);
        res1 = res;
      }
      if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        consumed = pos1;
        p4 = SlPos[0U];
        p_ = p4 + consumed;
        SlPos[0U] = p_;
        resultAfterSmoker = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterSmoker = res1;
      }
    }
    else
    {
      resultAfterSmoker = EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
  }
  else
  {
    resultAfterSmoker = resultAfterage;
  }
  if (resultAfterSmoker == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterSmoker;
  }
  ErrorHandlerFn("_smoker",
    "age",
    EverParseErrorReasonOfResult(resultAfterSmoker),
    resultAfterSmoker,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartSmoker);
  return resultAfterSmoker;
}

