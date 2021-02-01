

#include "Triangle2.h"

/*
Auto-generated field identifier for error reporting
*/
#define POINT__X ((uint64_t)1U)

/*
Auto-generated field identifier for error reporting
*/
#define POINT__Y ((uint64_t)2U)

/*
Auto-generated field identifier for error reporting
*/
#define TRIANGLE__CORNERS ((uint64_t)3U)

static inline uint64_t ValidatePointX(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _point_x
        of type Triangle2._point
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
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, POINT__X);
}

static inline uint64_t ValidatePointY(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _point_y
        of type Triangle2._point
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
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, POINT__Y);
}

inline uint64_t Triangle2ValidatePoint(uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
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

static inline uint64_t ValidateTriangleCorners(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _triangle_corners
        of type Triangle2._triangle
--*/
{
  /* Validating field corners */
  uint64_t endPositionOrError;
  if ((uint32_t)4U * (uint32_t)(uint8_t)3U % (uint32_t)4U == (uint32_t)0U)
  {
    if (((uint64_t)InputLength - StartPosition) < (uint64_t)((uint32_t)4U * (uint32_t)(uint8_t)3U))
    {
      endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    else
    {
      endPositionOrError = StartPosition + (uint64_t)((uint32_t)4U * (uint32_t)(uint8_t)3U);
    }
  }
  else
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, TRIANGLE__CORNERS);
}

uint64_t
Triangle2ValidateTriangle(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _triangle_corners */
  return ValidateTriangleCorners(InputLength, StartPosition);
}

