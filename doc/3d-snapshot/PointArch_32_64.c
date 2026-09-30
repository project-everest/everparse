

#include "PointArch_32_64.h"

#include "EverParse.h"

static inline uint64_t
ValidateInt(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytesForX0;
  uint64_t positionAfterX0;
  BOOLEAN hasBytesForX;
  uint64_t positionAfterX;
  #if ARCH64
  {
    KRML_MAYBE_UNUSED_VAR(positionAfterX);
    KRML_MAYBE_UNUSED_VAR(hasBytesForX);
    /* Validating field x */
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    hasBytesForX0 = (InputLen - StartPosition) >= 8ULL;
    if (hasBytesForX0)
    {
      positionAfterX0 = StartPosition + 8ULL;
    }
    else
    {
      positionAfterX0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterX0))
    {
      return positionAfterX0;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterX0),
      EverParseGetValidatorErrorKind(positionAfterX0),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterX0;
  }
  #else
  {
    KRML_MAYBE_UNUSED_VAR(positionAfterX0);
    KRML_MAYBE_UNUSED_VAR(hasBytesForX0);
    /* Validating field x */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    hasBytesForX = (InputLen - StartPosition) >= 4ULL;
    if (hasBytesForX)
    {
      positionAfterX = StartPosition + 4ULL;
    }
    else
    {
      positionAfterX =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterX))
    {
      return positionAfterX;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterX),
      EverParseGetValidatorErrorKind(positionAfterX),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterX;
  }
  #endif
}

uint64_t
PointArch3264ValidatePoint(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field x */
  uint64_t
  positionAfterX0 = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfterX;
  uint64_t positionAfterY;
  if (EverParseIsSuccess(positionAfterX0))
  {
    positionAfterX = positionAfterX0;
  }
  else
  {
    ErrorHandlerFn("_POINT",
      "x",
      EverParseErrorReasonOfResult(positionAfterX0),
      EverParseGetValidatorErrorKind(positionAfterX0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterX = positionAfterX0;
  }
  if (EverParseIsError(positionAfterX))
  {
    return positionAfterX;
  }
  /* Validating field y */
  positionAfterY = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, positionAfterX);
  if (EverParseIsSuccess(positionAfterY))
  {
    return positionAfterY;
  }
  ErrorHandlerFn("_POINT",
    "y",
    EverParseErrorReasonOfResult(positionAfterY),
    EverParseGetValidatorErrorKind(positionAfterY),
    Ctxt,
    Input,
    positionAfterX);
  return positionAfterY;
}

