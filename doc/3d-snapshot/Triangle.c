

#include "Triangle.h"

static inline uint64_t
ValidatePoint(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength - StartPosition);
  uint64_t positionAfterPoint;
  if (hasBytes0)
  {
    positionAfterPoint = StartPosition + 2ULL;
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
    ErrorHandlerFn("_point",
      "x",
      EverParseErrorReasonOfResult(positionAfterPoint),
      EverParseGetValidatorErrorKind(positionAfterPoint),
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
  BOOLEAN hasBytes = 2ULL <= (InputLength - positionAfterx);
  uint64_t positionAfterPoint0;
  if (hasBytes)
  {
    positionAfterPoint0 = positionAfterx + 2ULL;
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
  ErrorHandlerFn("_point",
    "y",
    EverParseErrorReasonOfResult(positionAfterPoint0),
    EverParseGetValidatorErrorKind(positionAfterPoint0),
    Ctxt,
    Input,
    positionAfterx);
  return positionAfterPoint0;
}

uint64_t
TriangleValidateTriangle(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field a */
  uint64_t
  positionAfterTriangle = ValidatePoint(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAftera;
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    positionAftera = positionAfterTriangle;
  }
  else
  {
    ErrorHandlerFn("_triangle",
      "a",
      EverParseErrorReasonOfResult(positionAfterTriangle),
      EverParseGetValidatorErrorKind(positionAfterTriangle),
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
  uint64_t
  positionAfterTriangle0 =
    ValidatePoint(Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAftera);
  uint64_t positionAfterb;
  if (EverParseIsSuccess(positionAfterTriangle0))
  {
    positionAfterb = positionAfterTriangle0;
  }
  else
  {
    ErrorHandlerFn("_triangle",
      "b",
      EverParseErrorReasonOfResult(positionAfterTriangle0),
      EverParseGetValidatorErrorKind(positionAfterTriangle0),
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
  uint64_t
  positionAfterTriangle1 =
    ValidatePoint(Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAfterb);
  if (EverParseIsSuccess(positionAfterTriangle1))
  {
    return positionAfterTriangle1;
  }
  ErrorHandlerFn("_triangle",
    "c",
    EverParseErrorReasonOfResult(positionAfterTriangle1),
    EverParseGetValidatorErrorKind(positionAfterTriangle1),
    Ctxt,
    Input,
    positionAfterb);
  return positionAfterTriangle1;
}

