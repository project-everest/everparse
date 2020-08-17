

#include "Triangle2.h"

/*
Auto-generated field identifier for error reporting
*/
#define TRIANGLE__CORNERS ((uint64_t)3U)

static inline uint64_t ValidateTriangleCorners(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _triangle_corners
        of type _triangle
--*/
{
  /* Validating field corners */
  uint64_t endPositionOrError;
  if ((uint32_t)(uint8_t)3U % (uint32_t)4U == (uint32_t)0U)
  {
    if (((uint64_t)Input.len - StartPosition) < (uint64_t)(uint32_t)(uint8_t)3U)
    {
      endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    else
    {
      endPositionOrError = StartPosition + (uint64_t)(uint32_t)(uint8_t)3U;
    }
  }
  else
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, TRIANGLE__CORNERS);
}

uint64_t Triangle2ValidateTriangle(InputBuffer Input, uint64_t StartPosition)
{
  /* Field _triangle_corners */
  return ValidateTriangleCorners(Input, StartPosition);
}

