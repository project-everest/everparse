

#include "EnumConstraint.h"

#include "EverParse.h"

uint8_t
EnumConstraintValidateEnumConstraint(
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
  uint64_t fieldStartEnumConstraint = (uint64_t)p;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)4U <= (rem - p0);
  uint8_t resultAftercol;
  uint8_t resultAfterEnumConstraint;
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
  uint32_t col;
  BOOLEAN colConstraintIsOk;
  size_t p2;
  uint64_t fieldStartEnumConstraint1;
  size_t pos1;
  size_t p02;
  size_t p3;
  size_t rem1;
  BOOLEAN hasBytes1;
  uint8_t resultAfterx_refinement;
  uint8_t resultAfterEnumConstraint0;
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
  uint32_t x_refinement;
  BOOLEAN x_refinementConstraintIsOk;
  if (hasBytes)
  {
    pos = p0 + (size_t)4U;
    resultAftercol = EVERPARSE_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftercol = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAftercol == EVERPARSE_VALIDATOR_SUCCESS)
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
    col = bfirst2 + n2 * 256U;
    colConstraintIsOk =
      col == ENUMCONSTRAINT_RED || col == ENUMCONSTRAINT_GREEN || col == ENUMCONSTRAINT_BLUE;
    if (colConstraintIsOk)
    {
      /* Validating field x */
      p2 = SlPos[0U];
      fieldStartEnumConstraint1 = (uint64_t)p2;
      pos1 = (size_t)0U;
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      p02 = pos1;
      p3 = SlPos[0U];
      rem1 = SlLen - p3;
      hasBytes1 = p02 <= rem1 && (size_t)4U <= (rem1 - p02);
      if (hasBytes1)
      {
        pos1 = p02 + (size_t)4U;
        resultAfterx_refinement = EVERPARSE_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterx_refinement = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (resultAfterx_refinement == EVERPARSE_VALIDATOR_SUCCESS)
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
        x_refinement = bfirst5 + n5 * 256U;
        /* start: checking constraint */
        x_refinementConstraintIsOk = x_refinement == 0U || col == ENUMCONSTRAINT_GREEN;
        /* end: checking constraint */
        resultAfterEnumConstraint0 =
          x_refinementConstraintIsOk ? EVERPARSE_VALIDATOR_SUCCESS
                                     : EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
      else
      {
        resultAfterEnumConstraint0 = resultAfterx_refinement;
      }
      if (resultAfterEnumConstraint0 == EVERPARSE_VALIDATOR_SUCCESS)
      {
        resultAfterEnumConstraint = resultAfterEnumConstraint0;
      }
      else
      {
        ErrorHandlerFn("_enum_constraint",
          "x.refinement",
          EverParseErrorReasonOfResult(resultAfterEnumConstraint0),
          resultAfterEnumConstraint0,
          Ctxt,
          SlBase,
          SlLen,
          SlPos,
          fieldStartEnumConstraint1);
        resultAfterEnumConstraint = resultAfterEnumConstraint0;
      }
    }
    else
    {
      resultAfterEnumConstraint = EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
  }
  else
  {
    resultAfterEnumConstraint = resultAftercol;
  }
  if (resultAfterEnumConstraint == EVERPARSE_VALIDATOR_SUCCESS)
  {
    return resultAfterEnumConstraint;
  }
  ErrorHandlerFn("_enum_constraint",
    "col",
    EverParseErrorReasonOfResult(resultAfterEnumConstraint),
    resultAfterEnumConstraint,
    Ctxt,
    SlBase,
    SlLen,
    SlPos,
    fieldStartEnumConstraint);
  return resultAfterEnumConstraint;
}

