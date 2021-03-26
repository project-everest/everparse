

#include "HelloWorld.h"

/*
Auto-generated field identifier for error reporting
*/
#define HELLOWORLD__POINT__X ((uint64_t)31U)

/*
Auto-generated field identifier for error reporting
*/
#define HELLOWORLD__POINT__Y ((uint64_t)32U)

static inline uint64_t ValidatePointX(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _point_x
        of type HelloWorld._point
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
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, HELLOWORLD__POINT__X);
}

static inline uint64_t ValidatePointY(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _point_y
        of type HelloWorld._point
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
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, HELLOWORLD__POINT__Y);
}

uint64_t HelloWorldValidatePoint(uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
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

