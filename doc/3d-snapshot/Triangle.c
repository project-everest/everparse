

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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _point_x
        of type Triangle._point
--*/
{
  /* Validating field x */
  uint32_t positionBeforePoint = *Input.pos;
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - currentPosition);
  uint64_t resultAfterPoint;
  if (hasBytes)
  {
    resultAfterPoint = (uint64_t)(uint32_t)2U;
  }
  else
  {
    resultAfterPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterPoint))
  {
    return resultAfterPoint;
  }
  Err("_point",
    "_point_x",
    EverParseErrorReasonOfResult(resultAfterPoint),
    Ctxt,
    Input,
    positionBeforePoint);
  return resultAfterPoint;
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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _point_y
        of type Triangle._point
--*/
{
  /* Validating field y */
  uint32_t positionBeforePoint = *Input.pos;
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - currentPosition);
  uint64_t resultAfterPoint;
  if (hasBytes)
  {
    resultAfterPoint = (uint64_t)(uint32_t)2U;
  }
  else
  {
    resultAfterPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterPoint))
  {
    return resultAfterPoint;
  }
  Err("_point",
    "_point_y",
    EverParseErrorReasonOfResult(resultAfterPoint),
    Ctxt,
    Input,
    positionBeforePoint);
  return resultAfterPoint;
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
  EverParseInputBuffer Input
)
{
  /* Field _point_x */
  uint32_t positionBeforePoint = *Input.pos;
  uint64_t resultAfterPoint = ValidatePointX(Ctxt, Err, Input);
  uint64_t res0;
  if (EverParseIsSuccess(resultAfterPoint))
  {
    res0 = resultAfterPoint;
  }
  else
  {
    Err("_point",
      "x",
      EverParseErrorReasonOfResult(resultAfterPoint),
      Ctxt,
      Input,
      positionBeforePoint);
    res0 = resultAfterPoint;
  }
  if (EverParseIsSuccess(res0))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res0;
  }
  uint64_t resultAfterx = res0;
  if (EverParseIsError(resultAfterx))
  {
    return resultAfterx;
  }
  /* Field _point_y */
  uint32_t positionBeforePoint0 = *Input.pos;
  uint64_t resultAfterPoint0 = ValidatePointY(Ctxt, Err, Input);
  uint64_t res;
  if (EverParseIsSuccess(resultAfterPoint0))
  {
    res = resultAfterPoint0;
  }
  else
  {
    Err("_point",
      "y",
      EverParseErrorReasonOfResult(resultAfterPoint0),
      Ctxt,
      Input,
      positionBeforePoint0);
    res = resultAfterPoint0;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _triangle_a
        of type Triangle._triangle
--*/
{
  /* Validating field a */
  uint32_t positionBeforeTriangle = *Input.pos;
  uint64_t resultAfterTriangle = ValidatePoint(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterTriangle))
  {
    return resultAfterTriangle;
  }
  Err("_triangle",
    "_triangle_a",
    EverParseErrorReasonOfResult(resultAfterTriangle),
    Ctxt,
    Input,
    positionBeforeTriangle);
  return resultAfterTriangle;
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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _triangle_b
        of type Triangle._triangle
--*/
{
  /* Validating field b */
  uint32_t positionBeforeTriangle = *Input.pos;
  uint64_t resultAfterTriangle = ValidatePoint(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterTriangle))
  {
    return resultAfterTriangle;
  }
  Err("_triangle",
    "_triangle_b",
    EverParseErrorReasonOfResult(resultAfterTriangle),
    Ctxt,
    Input,
    positionBeforeTriangle);
  return resultAfterTriangle;
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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _triangle_c
        of type Triangle._triangle
--*/
{
  /* Validating field c */
  uint32_t positionBeforeTriangle = *Input.pos;
  uint64_t resultAfterTriangle = ValidatePoint(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterTriangle))
  {
    return resultAfterTriangle;
  }
  Err("_triangle",
    "_triangle_c",
    EverParseErrorReasonOfResult(resultAfterTriangle),
    Ctxt,
    Input,
    positionBeforeTriangle);
  return resultAfterTriangle;
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
  EverParseInputBuffer Input
)
{
  /* Field _triangle_a */
  uint32_t positionBeforeTriangle = *Input.pos;
  uint64_t resultAfterTriangle = ValidateTriangleA(Ctxt, Err, Input);
  uint64_t resultAftera;
  if (EverParseIsSuccess(resultAfterTriangle))
  {
    resultAftera = resultAfterTriangle;
  }
  else
  {
    Err("_triangle",
      "a",
      EverParseErrorReasonOfResult(resultAfterTriangle),
      Ctxt,
      Input,
      positionBeforeTriangle);
    resultAftera = resultAfterTriangle;
  }
  if (EverParseIsError(resultAftera))
  {
    return resultAftera;
  }
  /* Field _triangle_b */
  uint32_t positionBeforeTriangle0 = *Input.pos;
  uint64_t resultAfterTriangle0 = ValidateTriangleB(Ctxt, Err, Input);
  uint64_t resultAfterb;
  if (EverParseIsSuccess(resultAfterTriangle0))
  {
    resultAfterb = resultAfterTriangle0;
  }
  else
  {
    Err("_triangle",
      "b",
      EverParseErrorReasonOfResult(resultAfterTriangle0),
      Ctxt,
      Input,
      positionBeforeTriangle0);
    resultAfterb = resultAfterTriangle0;
  }
  if (EverParseIsError(resultAfterb))
  {
    return resultAfterb;
  }
  /* Field _triangle_c */
  uint32_t positionBeforeTriangle1 = *Input.pos;
  uint64_t resultAfterTriangle1 = ValidateTriangleC(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterTriangle1))
  {
    return resultAfterTriangle1;
  }
  Err("_triangle",
    "c",
    EverParseErrorReasonOfResult(resultAfterTriangle1),
    Ctxt,
    Input,
    positionBeforeTriangle1);
  return resultAfterTriangle1;
}

