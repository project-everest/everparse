

#include "PointArch_32_64.h"

static inline uint64_t
ValidateInt(
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
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes0;
  uint64_t positionAfterInt;
  BOOLEAN hasBytes;
  uint64_t positionAfterInt0;
  #if ARCH64
  {
    KRML_MAYBE_UNUSED_VAR(positionAfterInt0);
    KRML_MAYBE_UNUSED_VAR(hasBytes);
    /* Validating field x */
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    hasBytes0 = 8ULL <= (InputLen - StartPosition);
    if (hasBytes0)
    {
      positionAfterInt = StartPosition + 8ULL;
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
    KRML_MAYBE_UNUSED_VAR(positionAfterInt);
    KRML_MAYBE_UNUSED_VAR(hasBytes0);
    /* Validating field x */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    hasBytes = 4ULL <= (InputLen - StartPosition);
    if (hasBytes)
    {
      positionAfterInt0 = StartPosition + 4ULL;
    }
    else
    {
      positionAfterInt0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterInt0))
    {
      return positionAfterInt0;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterInt0),
      EverParseGetValidatorErrorKind(positionAfterInt0),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterInt0;
  }
  #endif
}

uint64_t
PointArch3264ValidatePoint(
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
  uint64_t
  positionAfterPoint = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfterx;
  uint64_t positionAfterPoint0;
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

