

#include "Triangle.h"

/*
Auto-generated field identifier for error reporting
*/
#define TRIANGLE__POINT__X ((uint64_t)43U)

/*
Auto-generated field identifier for error reporting
*/
#define TRIANGLE__POINT__Y ((uint64_t)44U)

static inline uint64_t ValidatePointX(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _point_x
        of type Triangle._point
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
  return EverParseMaybeSetErrorCode(result, startPosition1, TRIANGLE__POINT__X);
}

static inline uint64_t ValidatePointY(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _point_y
        of type Triangle._point
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
  return EverParseMaybeSetErrorCode(result, startPosition1, TRIANGLE__POINT__Y);
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

static inline uint64_t ValidateTriangleA(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _triangle_a
        of type Triangle._triangle
--*/
{
  /* Validating field a */
  return ValidatePoint(Input);
}

static inline uint64_t ValidateTriangleB(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _triangle_b
        of type Triangle._triangle
--*/
{
  /* Validating field b */
  return ValidatePoint(Input);
}

static inline uint64_t ValidateTriangleC(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _triangle_c
        of type Triangle._triangle
--*/
{
  /* Validating field c */
  return ValidatePoint(Input);
}

uint64_t TriangleValidateTriangle(EverParseInputBuffer Input)
{
  /* Field _triangle_a */
  uint64_t resultAftera = ValidateTriangleA(Input);
  if (EverParseIsError(resultAftera))
  {
    return resultAftera;
  }
  /* Field _triangle_b */
  uint64_t resultAfterb = ValidateTriangleB(Input);
  if (EverParseIsError(resultAfterb))
  {
    return resultAfterb;
  }
  /* Field _triangle_c */
  return ValidateTriangleC(Input);
}

