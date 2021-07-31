

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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _point_x
        of type Triangle._point
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - Pos);
  uint64_t positionAfterPoint;
  if (hasBytes)
  {
    positionAfterPoint = (uint64_t)(Pos + (uint32_t)2U);
  }
  else
  {
    positionAfterPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  Err("_point", "_point_x", EverParseErrorReasonOfResult(positionAfterPoint), Ctxt, Input, Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _point_y
        of type Triangle._point
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - Pos);
  uint64_t positionAfterPoint;
  if (hasBytes)
  {
    positionAfterPoint = (uint64_t)(Pos + (uint32_t)2U);
  }
  else
  {
    positionAfterPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  Err("_point", "_point_y", EverParseErrorReasonOfResult(positionAfterPoint), Ctxt, Input, Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
{
  /* Field _point_x */
  uint64_t positionAfterPoint = ValidatePointX(Ctxt, Err, Input, Pos);
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterPoint))
  {
    res0 = positionAfterPoint;
  }
  else
  {
    Err("_point", "x", EverParseErrorReasonOfResult(positionAfterPoint), Ctxt, Input, Pos);
    res0 = positionAfterPoint;
  }
  if (EverParseIsSuccess(res0))
  {
    
  }
  uint64_t positionAfterx = res0;
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _point_y */
  uint64_t positionAfterPoint0 = ValidatePointY(Ctxt, Err, Input, (uint32_t)positionAfterx);
  uint64_t res;
  if (EverParseIsSuccess(positionAfterPoint0))
  {
    res = positionAfterPoint0;
  }
  else
  {
    Err("_point",
      "y",
      EverParseErrorReasonOfResult(positionAfterPoint0),
      Ctxt,
      Input,
      (uint32_t)positionAfterx);
    res = positionAfterPoint0;
  }
  if (EverParseIsSuccess(res))
  {
    
  }
  return res;
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _triangle_a
        of type Triangle._triangle
--*/
{
  /* Validating field a */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_a",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Input,
    Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _triangle_b
        of type Triangle._triangle
--*/
{
  /* Validating field b */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_b",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Input,
    Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _triangle_c
        of type Triangle._triangle
--*/
{
  /* Validating field c */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_c",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Input,
    Pos);
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
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
{
  /* Field _triangle_a */
  uint64_t positionAfterTriangle = ValidateTriangleA(Ctxt, Err, Input, Pos);
  uint64_t positionAftera;
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    positionAftera = positionAfterTriangle;
  }
  else
  {
    Err("_triangle", "a", EverParseErrorReasonOfResult(positionAfterTriangle), Ctxt, Input, Pos);
    positionAftera = positionAfterTriangle;
  }
  if (EverParseIsError(positionAftera))
  {
    return positionAftera;
  }
  /* Field _triangle_b */
  uint64_t
  positionAfterTriangle0 = ValidateTriangleB(Ctxt, Err, Input, (uint32_t)positionAftera);
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
      (uint32_t)positionAftera);
    positionAfterb = positionAfterTriangle0;
  }
  if (EverParseIsError(positionAfterb))
  {
    return positionAfterb;
  }
  /* Field _triangle_c */
  uint64_t
  positionAfterTriangle1 = ValidateTriangleC(Ctxt, Err, Input, (uint32_t)positionAfterb);
  if (EverParseIsSuccess(positionAfterTriangle1))
  {
    return positionAfterTriangle1;
  }
  Err("_triangle",
    "c",
    EverParseErrorReasonOfResult(positionAfterTriangle1),
    Ctxt,
    Input,
    (uint32_t)positionAfterb);
  return positionAfterTriangle1;
}

