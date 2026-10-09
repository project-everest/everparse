

#include "Smoker.h"

#include "EverParse.h"

uint8_t
SmokerValidateSmoker(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartSmoker = (uint64_t)p1;
  uint64_t startPositionSmoker = fieldStartSmoker;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t resultAfterage;
  uint8_t resultAfterSmoker;
  size_t p01;
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
  uint32_t res0;
  uint32_t age;
  BOOLEAN ageConstraintIsOk;
  size_t pos1;
  size_t p3;
  uint64_t viewStart;
  size_t fieldOff;
  uint64_t startPos;
  size_t p0;
  size_t p4;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res1;
  uint8_t res;
  size_t consumed;
  size_t p;
  size_t p_;
  if (hasBytes0)
  {
    pos = p00 + (size_t)4U;
    resultAfterage = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterage = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterage == EVERPARSE_VALIDATOR_SUCCESS)
  {
    p01 = *SlPos;
    m = p01 + (size_t)4U;
    sub = SlBase + p01;
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
    res0 = bfirst + n * 256U;
    *SlPos = m;
    age = res0;
    ageConstraintIsOk = age >= 21U;
    if (ageConstraintIsOk)
    {
      pos1 = (size_t)0U;
      /* Validating field cigarettesConsumed */
      p3 = *SlPos;
      viewStart = (uint64_t)p3;
      fieldOff = pos1;
      startPos = viewStart + (uint64_t)fieldOff;
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      p0 = pos1;
      p4 = *SlPos;
      rem = SlLen - p4;
      hasBytes = p0 <= rem && (size_t)1U <= (rem - p0);
      if (hasBytes)
      {
        pos1 = p0 + (size_t)1U;
        res1 = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        res1 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (res1 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        res = res1;
      }
      else
      {
        ErrorHandlerFn("_smoker",
          "cigarettesConsumed",
          EverParseErrorReasonOfResult(res1),
          res1,
          Ctxt,
          SlBase,
          SlLen,
          SlPos,
          startPos);
        res = res1;
      }
      if (res == EVERPARSE_VALIDATOR_SUCCESS)
      {
        consumed = pos1;
        p = *SlPos;
        p_ = p + consumed;
        *SlPos = p_;
        resultAfterSmoker = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterSmoker = res;
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
    startPositionSmoker);
  return resultAfterSmoker;
}

