

#include "Triangle2.h"

/*
Auto-generated field identifier for error reporting
*/
#define TRIANGLE2__TRIANGLE__CORNERS ((uint64_t)47U)

typedef uint8_t *Dtuple2_uint8T___;

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
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      TRIANGLE2__TRIANGLE__CORNERS);
}

uint64_t
Triangle2ValidateTriangle(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _triangle_corners */
  return ValidateTriangleCorners(InputLength, StartPosition);
}

