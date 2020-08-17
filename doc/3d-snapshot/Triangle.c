

#include "Triangle.h"

/*
Auto-generated field identifier for error reporting
*/
#define POINT__X ((uint64_t)1U)

/*
Auto-generated field identifier for error reporting
*/
#define POINT__Y ((uint64_t)2U)

static inline uint64_t ValidatePointX(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _point_x
        of type _point
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)Input.len - StartPosition) < (uint64_t)2U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)2U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, POINT__X);
}

static inline uint64_t ValidatePointY(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _point_y
        of type _point
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)Input.len - StartPosition) < (uint64_t)2U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)2U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, POINT__Y);
}

static inline uint64_t ValidatePoint(InputBuffer Input, uint64_t StartPosition)
{
  /* Field _point_x */
  uint64_t positionAfterx = ValidatePointX(Input, StartPosition);
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _point_y */
  return ValidatePointY(Input, positionAfterx);
}

static inline uint64_t ValidateTriangleA(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _triangle_a
        of type _triangle
--*/
{
  /* Validating field a */
  return ValidatePoint(Input, StartPosition);
}

static inline uint64_t ValidateTriangleB(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _triangle_b
        of type _triangle
--*/
{
  /* Validating field b */
  return ValidatePoint(Input, StartPosition);
}

static inline uint64_t ValidateTriangleC(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _triangle_c
        of type _triangle
--*/
{
  /* Validating field c */
  return ValidatePoint(Input, StartPosition);
}

uint64_t TriangleValidateTriangle(InputBuffer Input, uint64_t StartPosition)
{
  /* Field _triangle_a */
  uint64_t positionAftera = ValidateTriangleA(Input, StartPosition);
  if (EverParseIsError(positionAftera))
  {
    return positionAftera;
  }
  /* Field _triangle_b */
  uint64_t positionAfterb = ValidateTriangleB(Input, positionAftera);
  if (EverParseIsError(positionAfterb))
  {
    return positionAfterb;
  }
  /* Field _triangle_c */
  return ValidateTriangleC(Input, positionAfterb);
}

