

#include "Triangle2.h"

static inline uint64_t
ValidateTriangleCorners(
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
        Validator for field _triangle_corners
        of type Triangle2._triangle
--*/
{
  /* Validating field corners */
  uint32_t positionBeforeTriangle = *Input.pos;
  uint64_t res;
  if ((uint32_t)4U * (uint32_t)(uint8_t)3U % (uint32_t)4U == (uint32_t)0U)
  {
    uint32_t currentPosition = *Input.pos;
    BOOLEAN hasBytes = (uint32_t)4U * (uint32_t)(uint8_t)3U <= (Input.len - currentPosition);
    if (hasBytes)
    {
      res = (uint64_t)((uint32_t)4U * (uint32_t)(uint8_t)3U);
    }
    else
    {
      res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  uint64_t resultAfterTriangle = res;
  if (EverParseIsSuccess(resultAfterTriangle))
  {
    return resultAfterTriangle;
  }
  Err("_triangle",
    "_triangle_corners",
    EverParseErrorReasonOfResult(resultAfterTriangle),
    Ctxt,
    Input,
    positionBeforeTriangle);
  return resultAfterTriangle;
}

uint64_t
Triangle2ValidateTriangle(
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
  /* Field _triangle_corners */
  uint32_t positionBeforeTriangle = *Input.pos;
  uint64_t resultAfterTriangle = ValidateTriangleCorners(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterTriangle))
  {
    return resultAfterTriangle;
  }
  Err("_triangle",
    "corners",
    EverParseErrorReasonOfResult(resultAfterTriangle),
    Ctxt,
    Input,
    positionBeforeTriangle);
  return resultAfterTriangle;
}

