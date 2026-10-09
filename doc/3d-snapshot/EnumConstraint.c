

#include "EnumConstraint.h"

static uint8_t
ValidateCoreEnumConstraint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
)
{
  size_t p1 = *SlPos;
  uint64_t fieldStartEnumConstraint = (uint64_t)p1;
  uint64_t startPositionEnumConstraint = fieldStartEnumConstraint;
  size_t pos = (size_t)0U;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t p00 = pos;
  size_t p2 = *SlPos;
  size_t rem0 = SlLen - p2;
  BOOLEAN hasBytes0 = p00 <= rem0 && (size_t)4U <= (rem0 - p00);
  uint8_t resultAftercol;
  uint8_t resultAfterEnumConstraint;
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
  uint32_t col;
  BOOLEAN colConstraintIsOk;
  size_t p3;
  uint64_t fieldStartEnumConstraint1;
  uint64_t startPositionEnumConstraint1;
  size_t pos1;
  size_t p02;
  size_t p;
  size_t rem;
  BOOLEAN hasBytes;
  uint8_t resultAfterx_refinement;
  uint8_t resultAfterEnumConstraint0;
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
  uint32_t x_refinement;
  BOOLEAN x_refinementConstraintIsOk;
  if (hasBytes0)
  {
    pos = p00 + (size_t)4U;
    resultAftercol = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAftercol = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultAftercol == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
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
    col = res0;
    colConstraintIsOk =
      col == ENUMCONSTRAINT_RED || col == ENUMCONSTRAINT_GREEN || col == ENUMCONSTRAINT_BLUE;
    if (colConstraintIsOk)
    {
      /* Validating field x */
      p3 = *SlPos;
      fieldStartEnumConstraint1 = (uint64_t)p3;
      startPositionEnumConstraint1 = fieldStartEnumConstraint1;
      pos1 = (size_t)0U;
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      p02 = pos1;
      p = *SlPos;
      rem = SlLen - p;
      hasBytes = p02 <= rem && (size_t)4U <= (rem - p02);
      if (hasBytes)
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
        x_refinement = res;
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
          startPositionEnumConstraint1);
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
    startPositionEnumConstraint);
  return resultAfterEnumConstraint;
}

uint64_t
EnumConstraintValidateEnumConstraint(
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
  uint8_t status = ValidateCoreEnumConstraint(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

