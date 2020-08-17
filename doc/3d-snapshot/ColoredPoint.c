

#include "ColoredPoint.h"

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
#define COLOREDPOINT1__COLOR ((uint64_t)3U)

/*
Auto-generated field identifier for error reporting
*/
#define COLOREDPOINT2__COLOR ((uint64_t)4U)

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

static inline uint64_t ValidateColoredPoint1Color(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _coloredPoint1_color
        of type _coloredPoint1
--*/
{
  /* Validating field color */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint64_t endPositionOrError;
  if (((uint64_t)Input.len - StartPosition) < (uint64_t)1U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)1U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, COLOREDPOINT1__COLOR);
}

static inline uint64_t ValidateColoredPoint1Pt(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _coloredPoint1_pt
        of type _coloredPoint1
--*/
{
  /* Validating field pt */
  return ValidatePoint(Input, StartPosition);
}

uint64_t ColoredPointValidateColoredPoint1(InputBuffer Input, uint64_t StartPosition)
{
  /* Field _coloredPoint1_color */
  uint64_t positionAftercolor = ValidateColoredPoint1Color(Input, StartPosition);
  if (EverParseIsError(positionAftercolor))
  {
    return positionAftercolor;
  }
  /* Field _coloredPoint1_pt */
  return ValidateColoredPoint1Pt(Input, positionAftercolor);
}

static inline uint64_t ValidateColoredPoint2Pt(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _coloredPoint2_pt
        of type _coloredPoint2
--*/
{
  /* Validating field pt */
  return ValidatePoint(Input, StartPosition);
}

static inline uint64_t ValidateColoredPoint2Color(InputBuffer Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _coloredPoint2_color
        of type _coloredPoint2
--*/
{
  /* Validating field color */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint64_t endPositionOrError;
  if (((uint64_t)Input.len - StartPosition) < (uint64_t)1U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)1U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, COLOREDPOINT2__COLOR);
}

uint64_t ColoredPointValidateColoredPoint2(InputBuffer Input, uint64_t StartPosition)
{
  /* Field _coloredPoint2_pt */
  uint64_t positionAfterpt = ValidateColoredPoint2Pt(Input, StartPosition);
  if (EverParseIsError(positionAfterpt))
  {
    return positionAfterpt;
  }
  /* Field _coloredPoint2_color */
  return ValidateColoredPoint2Color(Input, positionAfterpt);
}

