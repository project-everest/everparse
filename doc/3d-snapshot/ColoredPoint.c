

#include "ColoredPoint.h"

/*
Auto-generated field identifier for error reporting
*/
#define COLOREDPOINT__POINT__X ((uint64_t)22U)

/*
Auto-generated field identifier for error reporting
*/
#define COLOREDPOINT__POINT__Y ((uint64_t)23U)

/*
Auto-generated field identifier for error reporting
*/
#define COLOREDPOINT__COLOREDPOINT1__COLOR ((uint64_t)24U)

/*
Auto-generated field identifier for error reporting
*/
#define COLOREDPOINT__COLOREDPOINT2__COLOR ((uint64_t)25U)

static inline uint64_t ValidatePointX(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _point_x
        of type ColoredPoint._point
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)2U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, COLOREDPOINT__POINT__X);
}

static inline uint64_t ValidatePointY(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _point_y
        of type ColoredPoint._point
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)2U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, COLOREDPOINT__POINT__Y);
}

static inline uint64_t ValidatePoint(EverParseInputBuffer Input)
{
  /* Field _point_x */
  uint64_t res = ValidatePointX(Input);
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  uint64_t resultAfterx = res;
  if (EverParseIsError(resultAfterx))
  {
    return resultAfterx;
  }
  /* Field _point_y */
  uint64_t res0 = ValidatePointY(Input);
  if (EverParseIsSuccess(res0))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res0;
  }
  return res0;
}

static inline uint64_t ValidateColoredPoint1Color(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _coloredPoint1_color
        of type ColoredPoint._coloredPoint1
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field color */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)1U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, COLOREDPOINT__COLOREDPOINT1__COLOR);
}

static inline uint64_t ValidateColoredPoint1Pt(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _coloredPoint1_pt
        of type ColoredPoint._coloredPoint1
--*/
{
  /* Validating field pt */
  return ValidatePoint(Input);
}

uint64_t ColoredPointValidateColoredPoint1(EverParseInputBuffer Input)
{
  /* Field _coloredPoint1_color */
  uint64_t res = ValidateColoredPoint1Color(Input);
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  uint64_t resultAftercolor = res;
  if (EverParseIsError(resultAftercolor))
  {
    return resultAftercolor;
  }
  /* Field _coloredPoint1_pt */
  return ValidateColoredPoint1Pt(Input);
}

static inline uint64_t ValidateColoredPoint2Pt(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _coloredPoint2_pt
        of type ColoredPoint._coloredPoint2
--*/
{
  /* Validating field pt */
  return ValidatePoint(Input);
}

static inline uint64_t ValidateColoredPoint2Color(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _coloredPoint2_color
        of type ColoredPoint._coloredPoint2
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field color */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)1U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, COLOREDPOINT__COLOREDPOINT2__COLOR);
}

uint64_t ColoredPointValidateColoredPoint2(EverParseInputBuffer Input)
{
  /* Field _coloredPoint2_pt */
  uint64_t resultAfterpt = ValidateColoredPoint2Pt(Input);
  if (EverParseIsError(resultAfterpt))
  {
    return resultAfterpt;
  }
  /* Field _coloredPoint2_color */
  uint64_t res = ValidateColoredPoint2Color(Input);
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

