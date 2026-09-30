

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
  uint64_t positionAfterXOrError0;
  BOOLEAN hasBytesForX;
  uint64_t positionAfterXOrError;
  #if ARCH64
  {
    KRML_MAYBE_UNUSED_VAR(positionAfterXOrError);
    KRML_MAYBE_UNUSED_VAR(hasBytesForX);
    /* Validating field x */
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    hasBytesForX0 = (InputLen - StartPosition) >= 8ULL;
    if (hasBytesForX0)
    {
      positionAfterXOrError0 = StartPosition + 8ULL;
    }
    else
    {
      positionAfterXOrError0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterXOrError0))
    {
      return positionAfterXOrError0;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterXOrError0),
      EverParseGetValidatorErrorKind(positionAfterXOrError0),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterXOrError0;
  }
  #else
  {
    KRML_MAYBE_UNUSED_VAR(positionAfterXOrError0);
    KRML_MAYBE_UNUSED_VAR(hasBytesForX0);
    /* Validating field x */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    hasBytesForX = (InputLen - StartPosition) >= 4ULL;
    if (hasBytesForX)
    {
      positionAfterXOrError = StartPosition + 4ULL;
    }
    else
    {
      positionAfterXOrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterXOrError))
    {
      return positionAfterXOrError;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterXOrError),
      EverParseGetValidatorErrorKind(positionAfterXOrError),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterXOrError;
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
  positionAfterXOrError = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfterX;
  uint64_t positionAfterYOrError;
  if (EverParseIsSuccess(positionAfterXOrError))
  {
    positionAfterX = positionAfterXOrError;
  }
  else
  {
    ErrorHandlerFn("_POINT",
      "x",
      EverParseErrorReasonOfResult(positionAfterXOrError),
      EverParseGetValidatorErrorKind(positionAfterXOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterX = positionAfterXOrError;
  }
  if (EverParseIsError(positionAfterX))
  {
    return positionAfterX;
  }
  /* Validating field y */
  positionAfterYOrError = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, positionAfterX);
  if (EverParseIsSuccess(positionAfterYOrError))
  {
    return positionAfterYOrError;
  }
  ErrorHandlerFn("_POINT",
    "y",
    EverParseErrorReasonOfResult(positionAfterYOrError),
    EverParseGetValidatorErrorKind(positionAfterYOrError),
    Ctxt,
    Input,
    positionAfterX);
  return positionAfterYOrError;
}

