

#include "Triangle.h"

/*
Auto-generated field identifier for error reporting
*/
#define TRIANGLE__POINT__X ((uint64_t)43U)

/*
Auto-generated field identifier for error reporting
*/
#define TRIANGLE__POINT__Y ((uint64_t)44U)

static inline uint64_t ValidatePointX(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _point_x
        of type Triangle._point
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)2U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)2U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, TRIANGLE__POINT__X);
}

static inline uint64_t ValidatePointY(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _point_y
        of type Triangle._point
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)2U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)2U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, TRIANGLE__POINT__Y);
}

static inline uint64_t ValidatePoint(uint32_t Uu, uint64_t StartPosition)
{
  /* Field _point_x */
  uint64_t positionAfterx = ValidatePointX(Uu, StartPosition);
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _point_y */
  return ValidatePointY(Uu, positionAfterx);
}

static inline uint64_t ValidateTriangleA(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _triangle_a
        of type Triangle._triangle
--*/
{
  /* Validating field a */
  return ValidatePoint(InputLength, StartPosition);
}

static inline uint64_t ValidateTriangleB(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _triangle_b
        of type Triangle._triangle
--*/
{
  /* Validating field b */
  return ValidatePoint(InputLength, StartPosition);
}

static inline uint64_t ValidateTriangleC(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _triangle_c
        of type Triangle._triangle
--*/
{
  /* Validating field c */
  return ValidatePoint(InputLength, StartPosition);
}

uint64_t TriangleValidateTriangle(uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _triangle_a */
  uint64_t positionAftera = ValidateTriangleA(Uu, StartPosition);
  if (EverParseIsError(positionAftera))
  {
    return positionAftera;
  }
  /* Field _triangle_b */
  uint64_t positionAfterb = ValidateTriangleB(Uu, positionAftera);
  if (EverParseIsError(positionAfterb))
  {
    return positionAfterb;
  }
  /* Field _triangle_c */
  return ValidateTriangleC(Uu, positionAfterb);
}

