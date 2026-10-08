

#include "Color.h"

#include "EverParse.h"

uint8_t
ColorValidateColoredPoint(
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
  /* Validating field col */
  size_t p = SlPos[0U];
  uint64_t fieldStartColoredPoint = (uint64_t)p;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t resultAftercol_refinement;
  uint8_t resultAfterColoredPoint;
  size_t p010;
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
  uint32_t col_refinement;
  BOOLEAN col_refinementConstraintIsOk;
  uint8_t resultAftercol_refinement1;
  size_t p2;
  uint64_t fieldStartColoredPoint1;
  size_t pos1;
  size_t p01;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t res;
  uint8_t resultAfterColoredPoint1;
  size_t consumed;
  size_t p4;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    resultAftercol_refinement = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftercol_refinement = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAftercol_refinement == EVERPARSE_VALIDATOR_SUCCESS)
  {
    /* reading field_value */
    p010 = SlPos[0U];
    m = p010 + (size_t)4U;
    sub = SlBase + p010;
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
    col_refinement = bfirst2 + n2 * 256U;
    /* start: checking constraint */
    col_refinementConstraintIsOk =
      COLOR_RED == col_refinement || COLOR_GREEN == col_refinement || COLOR_BLUE == col_refinement;
    /* end: checking constraint */
    resultAfterColoredPoint =
      col_refinementConstraintIsOk ? EVERPARSE_VALIDATOR_SUCCESS
                                   : EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
  }
  else
  {
    resultAfterColoredPoint = resultAftercol_refinement;
  }
  if (resultAfterColoredPoint == EVERPARSE_VALIDATOR_SUCCESS)
  {
    resultAftercol_refinement1 = resultAfterColoredPoint;
  }
  else
  {
    ErrorHandlerFn("_coloredPoint",
      "col.refinement",
      EverParseErrorReasonOfResult(resultAfterColoredPoint),
      resultAfterColoredPoint,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartColoredPoint);
    resultAftercol_refinement1 = resultAfterColoredPoint;
  }
  if (resultAftercol_refinement1 == EVERPARSE_VALIDATOR_SUCCESS)
  {
    p2 = SlPos[0U];
    fieldStartColoredPoint1 = (uint64_t)p2;
    pos1 = (size_t)0U;
    p01 = pos1;
    p3 = SlPos[0U];
    rem1 = SlLen - p3;
    hasBytes1 = p01 <= rem1 && (size_t)8U <= (rem1 - p01);
    if (hasBytes1)
    {
      pos1 = p01 + (size_t)8U;
      res = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    if (res == EVERPARSE_VALIDATOR_SUCCESS)
    {
      consumed = pos1;
      p4 = SlPos[0U];
      p_ = p4 + consumed;
      SlPos[0U] = p_;
      resultAfterColoredPoint1 = EVERPARSE_VALIDATOR_SUCCESS;
    }
    else
    {
      resultAfterColoredPoint1 = res;
    }
    if (resultAfterColoredPoint1 == EVERPARSE_VALIDATOR_SUCCESS)
    {
      return resultAfterColoredPoint1;
    }
    ErrorHandlerFn("_coloredPoint",
      "x",
      EverParseErrorReasonOfResult(resultAfterColoredPoint1),
      resultAfterColoredPoint1,
      Ctxt,
      SlBase,
      SlLen,
      SlPos,
      fieldStartColoredPoint1);
    return resultAfterColoredPoint1;
  }
  return resultAftercol_refinement1;
}

