

#include "HelloWorld.h"

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

uint64_t HelloWorldValidatePoint(InputBuffer Input, uint64_t StartPosition)
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

