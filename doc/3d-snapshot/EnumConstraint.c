

#include "EnumConstraint.h"

uint8_t
EnumConstraintValidateCoreEnumConstraint(
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
    resultAftercol = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftercol = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAftercol == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
        resultAfterx_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
      }
      else
      {
        resultAfterx_refinement = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
      }
      if (resultAfterx_refinement == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
          x_refinementConstraintIsOk ? EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS
                                     : EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
      }
      else
      {
        resultAfterEnumConstraint0 = resultAfterx_refinement;
      }
      if (resultAfterEnumConstraint0 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
      {
        resultAfterEnumConstraint = resultAfterEnumConstraint0;
      }
      else
      {
        ErrorHandlerFn("_enum_constraint",
          "x.refinement",
          EverParsePulseInternalErrorReasonOfResult(resultAfterEnumConstraint0),
          resultAfterEnumConstraint0 == 0U ||
            (resultAfterEnumConstraint0 >= 2U && resultAfterEnumConstraint0 <= 8U) ? (uint64_t)(uint32_t)resultAfterEnumConstraint0
                                                                                   : 15ULL,
          Ctxt,
          SlBase,
          fieldStartEnumConstraint1);
        resultAfterEnumConstraint = resultAfterEnumConstraint0;
      }
    }
    else
    {
      resultAfterEnumConstraint = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED;
    }
  }
  else
  {
    resultAfterEnumConstraint = resultAftercol;
  }
  if (resultAfterEnumConstraint == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterEnumConstraint;
  }
  ErrorHandlerFn("_enum_constraint",
    "col",
    EverParsePulseInternalErrorReasonOfResult(resultAfterEnumConstraint),
    resultAfterEnumConstraint == 0U ||
      (resultAfterEnumConstraint >= 2U && resultAfterEnumConstraint <= 8U) ? (uint64_t)(uint32_t)resultAfterEnumConstraint
                                                                           : 15ULL,
    Ctxt,
    SlBase,
    fieldStartEnumConstraint);
  return resultAfterEnumConstraint;
}

uint64_t
EnumConstraintValidateEnumConstraint(
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
  uint8_t status = EnumConstraintValidateCoreEnumConstraint(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

