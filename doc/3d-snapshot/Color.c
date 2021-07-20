

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

static inline uint64_t ValidateColor(EverParseInputBuffer Input)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAftercolor;
  if (hasBytes)
  {
    resultAftercolor = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAftercolor = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsError(resultAftercolor))
  {
    return resultAftercolor;
  }
  /* reading field value */
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition0 = *Input.pos;
  uint8_t *res = Input.buf + currentPosition0;
  *Input.pos = currentPosition0 + (uint32_t)4U;
  uint8_t *temp1 = res;
  uint32_t res0 = Load32Le(temp1);
  uint32_t color = res0;
  /* start: checking constraint */
  BOOLEAN colorConstraintIsOk = color == RED || color == GREEN || color == BLUE || FALSE;
  /* end: checking constraint */
  return EverParseCheckConstraintOk(colorConstraintIsOk, resultAftercolor);
}

static inline uint64_t ValidateColoredPointCol(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _coloredPoint_col
        of type Color._coloredPoint
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field col */
  uint64_t result = ValidateColor(Input);
  return EverParseMaybeSetErrorCode(result, startPosition1, COLOR__COLOREDPOINT__COL);
}

static inline uint64_t ValidateColoredPointX(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _coloredPoint_x
        of type Color._coloredPoint
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field x */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, COLOR__COLOREDPOINT__X);
}

static inline uint64_t ValidateColoredPointY(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _coloredPoint_y
        of type Color._coloredPoint
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field y */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, COLOR__COLOREDPOINT__Y);
}

uint64_t ColorValidateColoredPoint(EverParseInputBuffer Input)
{
  /* Field _coloredPoint_col */
  uint64_t resultAftercol = ValidateColoredPointCol(Input);
  if (EverParseIsError(resultAftercol))
  {
    return resultAftercol;
  }
  /* Field _coloredPoint_x */
  uint64_t res = ValidateColoredPointX(Input);
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
  /* Field _coloredPoint_y */
  uint64_t res0 = ValidateColoredPointY(Input);
  if (EverParseIsSuccess(res0))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res0;
  }
  return res0;
}

