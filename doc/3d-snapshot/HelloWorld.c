

#include "HelloWorld.h"

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
        of type HelloWorld._point
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
        of type HelloWorld._point
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

uint64_t
HelloWorldValidatePoint(
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

