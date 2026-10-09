

#include "ReadPair.h"

static uint8_t
ValidateCorePair(
  uint32_t *X,
  uint32_t *Y,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field first */
  size_t p1 = *SlPos;
  uint64_t fieldStartPair = (uint64_t)p1;
  uint64_t startPositionPair = fieldStartPair;
  size_t pos0 = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos0;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t resultAfterfirst0;
  uint8_t resultAfterPair;
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
  uint32_t res0;
  uint32_t first4;
  BOOLEAN actionSuccessFirst;
  uint8_t resultAfterfirst;
  size_t p3;
  uint64_t fieldStartPair0;
  uint64_t startPositionPair0;
  size_t pos;
  size_t p02;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAftersecond;
  uint8_t resultAfterPair0;
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
  uint32_t second;
  BOOLEAN actionSuccessSecond;
  if (hasBytes0)
  {
    pos0 = p00 + (size_t)4U;
    resultAfterfirst0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterfirst0 = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAfterfirst0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
    res0 = bfirst2 + n2 * 256U;
    *SlPos = m0;
    first4 = res0;
    *X = first4;
    actionSuccessFirst = TRUE;
    resultAfterPair =
      actionSuccessFirst ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                         : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
  }
  else
  {
    resultAfterPair = resultAfterfirst0;
  }
  if (resultAfterPair == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAfterfirst = resultAfterPair;
  }
  else
  {
    ErrorHandlerFn("_Pair",
      "first",
      EverParsePulseInternalErrorReasonOfResult(resultAfterPair),
      resultAfterPair == 0U || (resultAfterPair >= 2U && resultAfterPair <= 8U) ? (uint64_t)(uint32_t)resultAfterPair
                                                                                : 15ULL,
      Ctxt,
      SlBase,
      startPositionPair);
    resultAfterfirst = resultAfterPair;
  }
  if (resultAfterfirst == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    /* Validating field second */
    p3 = *SlPos;
    fieldStartPair0 = (uint64_t)p3;
    startPositionPair0 = fieldStartPair0;
    pos = (size_t)0U;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    p02 = pos;
    p = *SlPos;
    rem = SlLen - p;
    hasBytes = p02 <= rem && (size_t)4U <= (rem - p02);
    if (hasBytes)
    {
      pos = p02 + (size_t)4U;
      resultAftersecond = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAftersecond = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (resultAftersecond == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
      res = bfirst + n * 256U;
      *SlPos = m;
      second = res;
      *Y = second;
      actionSuccessSecond = TRUE;
      resultAfterPair0 =
        actionSuccessSecond ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                            : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterPair0 = resultAftersecond;
    }
    if (resultAfterPair0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterPair0;
    }
    ErrorHandlerFn("_Pair",
      "second",
      EverParsePulseInternalErrorReasonOfResult(resultAfterPair0),
      resultAfterPair0 == 0U || (resultAfterPair0 >= 2U && resultAfterPair0 <= 8U) ? (uint64_t)(uint32_t)resultAfterPair0
                                                                                   : 15ULL,
      Ctxt,
      SlBase,
      startPositionPair0);
    return resultAfterPair0;
  }
  return resultAfterfirst;
}

uint64_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
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
  uint8_t status = ValidateCorePair(X, Y, Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

