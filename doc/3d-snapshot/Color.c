

#include "Color.h"

static uint8_t
ValidateCoreColoredPoint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  /* Validating field col */
  size_t p1 = *SlPos;
  uint64_t fieldStartColoredPoint = (uint64_t)p1;
  uint64_t startPositionColoredPoint = fieldStartColoredPoint;
  size_t pos0 = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos0;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t resultAftercol_refinement;
  uint8_t resultAfterColoredPoint;
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
  uint32_t col_refinement;
  BOOLEAN col_refinementConstraintIsOk;
  uint8_t resultAftercol_refinement0;
  size_t p3;
  uint64_t fieldStartColoredPoint0;
  uint64_t startPositionColoredPoint0;
  size_t pos;
  size_t p0;
  size_t p4;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t res;
  uint8_t resultAfterColoredPoint0;
  size_t consumed;
  size_t p;
  size_t p_;
  if (hasBytes0)
  {
    pos0 = p00 + (size_t)4U;
    resultAftercol_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftercol_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAftercol_refinement == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    /* reading field_value */
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
    col_refinement = res0;
    /* start: checking constraint */
    col_refinementConstraintIsOk =
      COLOR_RED == col_refinement || COLOR_GREEN == col_refinement || COLOR_BLUE == col_refinement;
    /* end: checking constraint */
    resultAfterColoredPoint =
      col_refinementConstraintIsOk ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                                   : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
  }
  else
  {
    resultAfterColoredPoint = resultAftercol_refinement;
  }
  if (resultAfterColoredPoint == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    resultAftercol_refinement0 = resultAfterColoredPoint;
  }
  else
  {
    ErrorHandlerFn("_coloredPoint",
      "col.refinement",
      EverParsePulseInternalErrorReasonOfResult(resultAfterColoredPoint),
      resultAfterColoredPoint == 0U ||
        (resultAfterColoredPoint >= 2U && resultAfterColoredPoint <= 8U) ? (uint64_t)(uint32_t)resultAfterColoredPoint
                                                                         : 15ULL,
      Ctxt,
      SlBase,
      startPositionColoredPoint);
    resultAftercol_refinement0 = resultAfterColoredPoint;
  }
  if (resultAftercol_refinement0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    p3 = *SlPos;
    fieldStartColoredPoint0 = (uint64_t)p3;
    startPositionColoredPoint0 = fieldStartColoredPoint0;
    pos = (size_t)0U;
    p0 = pos;
    p4 = *SlPos;
    rem = SlLen - p4;
    hasBytes = p0 <= rem && (size_t)8U <= (rem - p0);
    if (hasBytes)
    {
      pos = p0 + (size_t)8U;
      res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      consumed = pos;
      p = *SlPos;
      p_ = p + consumed;
      *SlPos = p_;
      resultAfterColoredPoint0 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterColoredPoint0 = res;
    }
    if (resultAfterColoredPoint0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
    {
      return resultAfterColoredPoint0;
    }
    ErrorHandlerFn("_coloredPoint",
      "x",
      EverParsePulseInternalErrorReasonOfResult(resultAfterColoredPoint0),
      resultAfterColoredPoint0 == 0U ||
        (resultAfterColoredPoint0 >= 2U && resultAfterColoredPoint0 <= 8U) ? (uint64_t)(uint32_t)resultAfterColoredPoint0
                                                                           : 15ULL,
      Ctxt,
      SlBase,
      startPositionColoredPoint0);
    return resultAfterColoredPoint0;
  }
  return resultAftercol_refinement0;
}

uint64_t
ColorValidateColoredPoint(
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
  uint8_t status = ValidateCoreColoredPoint(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

