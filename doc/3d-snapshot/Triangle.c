

#include "Triangle.h"



static inline uint64_t
ValidatePoint(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (uint64_t)2U <= (InputLength - StartPosition);
  uint64_t positionAfterPoint;
  if (hasBytes0)
  {
    positionAfterPoint = StartPosition + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterPoint))
  {
    res = positionAfterPoint;
  }
  else
  {
    Err("_point",
      "x",
      EverParseErrorReasonOfResult(positionAfterPoint),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterPoint;
  }
  uint64_t positionAfterx = res;
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint64_t)2U <= (InputLength - positionAfterx);
  uint64_t positionAfterPoint0;
  if (hasBytes)
  {
    positionAfterPoint0 = positionAfterx + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterx);
  }
  if (EverParseIsSuccess(positionAfterPoint0))
  {
    return positionAfterPoint0;
  }
  Err("_point",
    "y",
    EverParseErrorReasonOfResult(positionAfterPoint0),
    Ctxt,
    Input,
    positionAfterx);
  return positionAfterPoint0;
}

uint64_t
TriangleValidateTriangle(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field a */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Input, InputLength, StartPosition);
  uint64_t positionAftera;
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    positionAftera = positionAfterTriangle;
  }
  else
  {
    Err("_triangle",
      "a",
      EverParseErrorReasonOfResult(positionAfterTriangle),
      Ctxt,
      Input,
      StartPosition);
    positionAftera = positionAfterTriangle;
  }
  if (EverParseIsError(positionAftera))
  {
    return positionAftera;
  }
  /* Validating field b */
  uint64_t positionAfterTriangle0 = ValidatePoint(Ctxt, Err, Input, InputLength, positionAftera);
  uint64_t positionAfterb;
  if (EverParseIsSuccess(positionAfterTriangle0))
  {
    positionAfterb = positionAfterTriangle0;
  }
  else
  {
    Err("_triangle",
      "b",
      EverParseErrorReasonOfResult(positionAfterTriangle0),
      Ctxt,
      Input,
      positionAftera);
    positionAfterb = positionAfterTriangle0;
  }
  if (EverParseIsError(positionAfterb))
  {
    return positionAfterb;
  }
  /* Validating field c */
  uint64_t positionAfterTriangle1 = ValidatePoint(Ctxt, Err, Input, InputLength, positionAfterb);
  if (EverParseIsSuccess(positionAfterTriangle1))
  {
    return positionAfterTriangle1;
  }
  Err("_triangle",
    "c",
    EverParseErrorReasonOfResult(positionAfterTriangle1),
    Ctxt,
    Input,
    positionAfterb);
  return positionAfterTriangle1;
}

