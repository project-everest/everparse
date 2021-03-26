

#include "Color.h"

/*
Auto-generated field identifier for error reporting
*/
#define COLOR__COLOREDPOINT__COL ((uint64_t)19U)

/*
Auto-generated field identifier for error reporting
*/
#define COLOR__COLOREDPOINT__X ((uint64_t)20U)

/*
Auto-generated field identifier for error reporting
*/
#define COLOR__COLOREDPOINT__Y ((uint64_t)21U)

/*
Enum constant
*/
#define RED ((uint32_t)1U)

/*
Enum constant
*/
#define GREEN ((uint32_t)2U)

/*
Enum constant
*/
#define BLUE ((uint32_t)42U)

static inline uint64_t
ValidateColor(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAftercolor;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    positionAftercolor = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAftercolor = StartPosition + (uint64_t)4U;
  }
  if (EverParseIsError(positionAftercolor))
  {
    return positionAftercolor;
  }
  /* reading field value */
  uint8_t *base = Input;
  uint32_t color = Load32Le(base + (uint32_t)StartPosition);
  /* start: checking constraint */
  BOOLEAN colorConstraintIsOk = color == RED || color == GREEN || color == BLUE || FALSE;
  /* end: checking constraint */
  return EverParseCheckConstraintOk(colorConstraintIsOk, positionAftercolor);
}

static inline uint64_t
ValidateColoredPointCol(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _coloredPoint_col
        of type Color._coloredPoint
--*/
{
  /* Validating field col */
  uint64_t endPositionOrError = ValidateColor(InputLength, Input, StartPosition);
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, COLOR__COLOREDPOINT__COL);
}

static inline uint64_t ValidateColoredPointX(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _coloredPoint_x
        of type Color._coloredPoint
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, COLOR__COLOREDPOINT__X);
}

static inline uint64_t ValidateColoredPointY(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _coloredPoint_y
        of type Color._coloredPoint
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, COLOR__COLOREDPOINT__Y);
}

uint64_t ColorValidateColoredPoint(uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _coloredPoint_col */
  uint64_t positionAftercol = ValidateColoredPointCol(Uu, Input, StartPosition);
  if (EverParseIsError(positionAftercol))
  {
    return positionAftercol;
  }
  /* Field _coloredPoint_x */
  uint64_t positionAfterx = ValidateColoredPointX(Uu, positionAftercol);
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _coloredPoint_y */
  return ValidateColoredPointY(Uu, positionAfterx);
}

