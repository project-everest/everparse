

#include "Triangle.h"

static inline uint64_t
ValidatePointX(
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
/*++
    Internal helper function:
        Validator for field _point_x
        of type Triangle._point
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint64_t)2U <= (InputLength - StartPosition);
  uint64_t positionAfterPoint;
  if (hasBytes)
  {
    positionAfterPoint = StartPosition + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  Err("_point",
    "_point_x",
    EverParseErrorReasonOfResult(positionAfterPoint),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPoint;
}

static inline uint64_t
ValidatePointY(
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
/*++
    Internal helper function:
        Validator for field _point_y
        of type Triangle._point
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint64_t)2U <= (InputLength - StartPosition);
  uint64_t positionAfterPoint;
  if (hasBytes)
  {
    positionAfterPoint = StartPosition + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  Err("_point",
    "_point_y",
    EverParseErrorReasonOfResult(positionAfterPoint),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPoint;
}

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
  /* Field _point_x */
  uint64_t positionAfterPoint = ValidatePointX(Ctxt, Err, Input, InputLength, StartPosition);
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
  /* Field _point_y */
  uint64_t positionAfterPoint0 = ValidatePointY(Ctxt, Err, Input, InputLength, positionAfterx);
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

static inline uint64_t
ValidateTriangleA(
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
/*++
    Internal helper function:
        Validator for field _triangle_a
        of type Triangle._triangle
--*/
{
  /* Validating field a */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Input, InputLength, StartPosition);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_a",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTriangle;
}

static inline uint64_t
ValidateTriangleB(
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
/*++
    Internal helper function:
        Validator for field _triangle_b
        of type Triangle._triangle
--*/
{
  /* Validating field b */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Input, InputLength, StartPosition);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_b",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTriangle;
}

static inline uint64_t
ValidateTriangleC(
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
/*++
    Internal helper function:
        Validator for field _triangle_c
        of type Triangle._triangle
--*/
{
  /* Validating field c */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Input, InputLength, StartPosition);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_c",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTriangle;
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
  /* Field _triangle_a */
  uint64_t
  positionAfterTriangle = ValidateTriangleA(Ctxt, Err, Input, InputLength, StartPosition);
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
  /* Field _triangle_b */
  uint64_t
  positionAfterTriangle0 = ValidateTriangleB(Ctxt, Err, Input, InputLength, positionAftera);
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
  /* Field _triangle_c */
  uint64_t
  positionAfterTriangle1 = ValidateTriangleC(Ctxt, Err, Input, InputLength, positionAfterb);
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

