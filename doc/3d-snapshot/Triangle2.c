

#include "Triangle2.h"

/*
Auto-generated field identifier for error reporting
*/
#define TRIANGLE2__TRIANGLE__CORNERS ((uint64_t)47U)

static inline uint64_t ValidateTriangleCorners(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _triangle_corners
        of type Triangle2._triangle
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field corners */
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
  uint64_t result = res;
  return EverParseMaybeSetErrorCode(result, startPosition1, TRIANGLE2__TRIANGLE__CORNERS);
}

uint64_t Triangle2ValidateTriangle(EverParseInputBuffer Input)
{
  /* Field _triangle_corners */
  return ValidateTriangleCorners(Input);
}

