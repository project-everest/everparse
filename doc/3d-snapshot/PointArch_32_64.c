

#include "PointArch_32_64.h"



static inline uint64_t
ValidateInt(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  #if ARCH64
  {
    /* Validating field x */
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    BOOLEAN hasBytes = (uint64_t)8U <= (InputLen - StartPosition);
    uint64_t positionAfterInt;
    if (hasBytes)
    {
      positionAfterInt = StartPosition + (uint64_t)8U;
    }
    else
    {
      positionAfterInt =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterInt))
    {
      return positionAfterInt;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterInt),
      EverParseGetValidatorErrorKind(positionAfterInt),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterInt;
  }
  #else
  {
    /* Validating field x */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    BOOLEAN hasBytes = (uint64_t)4U <= (InputLen - StartPosition);
    uint64_t positionAfterInt;
    if (hasBytes)
    {
      positionAfterInt = StartPosition + (uint64_t)4U;
    }
    else
    {
      positionAfterInt =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterInt))
    {
      return positionAfterInt;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterInt),
      EverParseGetValidatorErrorKind(positionAfterInt),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterInt;
  }
  #endif
}

uint64_t
PointArch3264ValidatePoint(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
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
  uint64_t
  positionAfterPoint = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfterx;
  if (EverParseIsSuccess(positionAfterPoint))
  {
    positionAfterx = positionAfterPoint;
  }
  else
  {
    ErrorHandlerFn("_POINT",
      "x",
      EverParseErrorReasonOfResult(positionAfterPoint),
      EverParseGetValidatorErrorKind(positionAfterPoint),
      Ctxt,
      Input,
      StartPosition);
    positionAfterx = positionAfterPoint;
  }
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Validating field y */
  uint64_t
  positionAfterPoint0 = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, positionAfterx);
  if (EverParseIsSuccess(positionAfterPoint0))
  {
    return positionAfterPoint0;
  }
  ErrorHandlerFn("_POINT",
    "y",
    EverParseErrorReasonOfResult(positionAfterPoint0),
    EverParseGetValidatorErrorKind(positionAfterPoint0),
    Ctxt,
    Input,
    positionAfterx);
  return positionAfterPoint0;
}

