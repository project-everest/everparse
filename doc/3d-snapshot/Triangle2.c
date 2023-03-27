

#include "Triangle2.h"

static inline uint64_t
ValidatePoint(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (uint64_t)2U <= (InputLength - StartPosition);
  uint64_t positionAfterPoint;
  if (hasBytes0)
  {
    positionAfterPoint = StartPosition + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterPoint))
  {
    res = positionAfterPoint;
  }
  else
  {
    ErrorHandlerFn("_point",
      "x",
      EverParseErrorReasonOfResult(positionAfterPoint),
      EverParseGetValidatorErrorKind(positionAfterPoint),
      Ctxt,
      Input,
      StartPosition);
    res = positionAfterPoint;
  }
  uint64_t positionAfterx = res;
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint64_t)2U <= (InputLength - positionAfterx);
  uint64_t positionAfterPoint0;
  if (hasBytes)
  {
    positionAfterPoint0 = positionAfterx + (uint64_t)2U;
  }
  else
  {
    positionAfterPoint0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterx);
  }
  if (EverParseIsSuccess(positionAfterPoint0))
  {
    return positionAfterPoint0;
  }
  ErrorHandlerFn("_point",
    "y",
    EverParseErrorReasonOfResult(positionAfterPoint0),
    EverParseGetValidatorErrorKind(positionAfterPoint0),
    Ctxt,
    Input,
    positionAfterx);
  return positionAfterPoint0;
}

uint64_t
Triangle2ValidateTriangle(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field corners */
  BOOLEAN
  hasEnoughBytes =
    (uint64_t)((uint32_t)4U * (uint32_t)(uint8_t)3U)
    <= (InputLength - StartPosition);
  uint64_t positionAfterTriangle;
  if (!hasEnoughBytes)
  {
    positionAfterTriangle =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  else
  {
    uint8_t *truncatedInput = Input;
    uint64_t
    truncatedInputLength = StartPosition + (uint64_t)((uint32_t)4U * (uint32_t)(uint8_t)3U);
    uint64_t result = StartPosition;
    while (TRUE)
    {
      uint64_t position = result;
      BOOLEAN ite;
      if (!((uint64_t)1U <= (truncatedInputLength - position)))
      {
        ite = TRUE;
      }
      else
      {
        uint64_t
        positionAfterTriangle =
          ValidatePoint(Ctxt,
            ErrorHandlerFn,
            truncatedInput,
            truncatedInputLength,
            position);
        uint64_t result1;
        if (EverParseIsSuccess(positionAfterTriangle))
        {
          result1 = positionAfterTriangle;
        }
        else
        {
          ErrorHandlerFn("_triangle",
            "corners.element",
            EverParseErrorReasonOfResult(positionAfterTriangle),
            EverParseGetValidatorErrorKind(positionAfterTriangle),
            Ctxt,
            truncatedInput,
            position);
          result1 = positionAfterTriangle;
        }
        result = result1;
        ite = EverParseIsError(result1);
      }
      if (ite)
      {
        break;
      }
    }
    uint64_t res = result;
    positionAfterTriangle = res;
  }
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  ErrorHandlerFn("_triangle",
    "corners",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    EverParseGetValidatorErrorKind(positionAfterTriangle),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTriangle;
}

