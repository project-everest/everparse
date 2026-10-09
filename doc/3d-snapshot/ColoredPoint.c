

#include "ColoredPoint.h"

uint8_t
ColoredPointValidateCoreColoredPoint1(
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
  uint64_t fieldStartColoredPoint1 = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)5U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterColoredPoint1;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)5U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterColoredPoint1 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterColoredPoint1 = res;
  }
  if (resultAfterColoredPoint1 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterColoredPoint1;
  }
  ErrorHandlerFn("_coloredPoint1",
    "color",
    EverParsePulseInternalErrorReasonOfResult(resultAfterColoredPoint1),
    resultAfterColoredPoint1 == 0U ||
      (resultAfterColoredPoint1 >= 2U && resultAfterColoredPoint1 <= 8U) ? (uint64_t)(uint32_t)resultAfterColoredPoint1
                                                                         : 15ULL,
    Ctxt,
    SlBase,
    fieldStartColoredPoint1);
  return resultAfterColoredPoint1;
}

uint64_t
ColoredPointValidateColoredPoint1(
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
  uint8_t status = ColoredPointValidateCoreColoredPoint1(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

uint8_t
ColoredPointValidateCoreColoredPoint2(
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
  uint64_t fieldStartColoredPoint2 = (uint64_t)p;
  size_t pos = (size_t)0U;
  size_t p0 = pos;
  size_t p1 = SlPos[0U];
  size_t rem = SlLen - p1;
  BOOLEAN hasBytes = p0 <= rem && (size_t)5U <= (rem - p0);
  uint8_t res;
  uint8_t resultAfterColoredPoint2;
  size_t consumed;
  size_t p2;
  size_t p_;
  if (hasBytes)
  {
    pos = p0 + (size_t)5U;
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    res = EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (res == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    consumed = pos;
    p2 = SlPos[0U];
    p_ = p2 + consumed;
    SlPos[0U] = p_;
    resultAfterColoredPoint2 = EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS;
  }
  else
  {
    resultAfterColoredPoint2 = res;
  }
  if (resultAfterColoredPoint2 == EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS)
  {
    return resultAfterColoredPoint2;
  }
  ErrorHandlerFn("_coloredPoint2",
    "pt",
    EverParsePulseInternalErrorReasonOfResult(resultAfterColoredPoint2),
    resultAfterColoredPoint2 == 0U ||
      (resultAfterColoredPoint2 >= 2U && resultAfterColoredPoint2 <= 8U) ? (uint64_t)(uint32_t)resultAfterColoredPoint2
                                                                         : 15ULL,
    Ctxt,
    SlBase,
    fieldStartColoredPoint2);
  return resultAfterColoredPoint2;
}

uint64_t
ColoredPointValidateColoredPoint2(
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
  uint8_t status = ColoredPointValidateCoreColoredPoint2(Ctxt, Handler, Input, len, &cursor);
  size_t final = cursor;
  uint64_t position = (uint64_t)final;
  return
    (status == 0U || (status >= 2U && status <= 8U) ? (uint64_t)(uint32_t)status : 15ULL) *
      1152921504606846976ULL
    + position;
}

