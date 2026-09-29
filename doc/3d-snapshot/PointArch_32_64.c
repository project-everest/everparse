

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
  BOOLEAN hasBytes0;
  uint64_t positionAfterx0;
  BOOLEAN hasBytes;
  uint64_t positionAfterx;
  #if ARCH64
  {
    KRML_MAYBE_UNUSED_VAR(positionAfterx);
    KRML_MAYBE_UNUSED_VAR(hasBytes);
    /* Validating field x */
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    hasBytes0 = (InputLen - StartPosition) >= 8ULL;
    if (hasBytes0)
    {
      positionAfterx0 = StartPosition + 8ULL;
    }
    else
    {
      positionAfterx0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterx0))
    {
      return positionAfterx0;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterx0),
      EverParseGetValidatorErrorKind(positionAfterx0),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterx0;
  }
  #else
  {
    KRML_MAYBE_UNUSED_VAR(positionAfterx0);
    KRML_MAYBE_UNUSED_VAR(hasBytes0);
    /* Validating field x */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    hasBytes = (InputLen - StartPosition) >= 4ULL;
    if (hasBytes)
    {
      positionAfterx = StartPosition + 4ULL;
    }
    else
    {
      positionAfterx =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterx))
    {
      return positionAfterx;
    }
    ErrorHandlerFn("_INT",
      "x",
      EverParseErrorReasonOfResult(positionAfterx),
      EverParseGetValidatorErrorKind(positionAfterx),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterx;
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
  positionAfterx0 = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfterx;
  uint64_t positionAftery;
  if (EverParseIsSuccess(positionAfterx0))
  {
    positionAfterx = positionAfterx0;
  }
  else
  {
    ErrorHandlerFn("_POINT",
      "x",
      EverParseErrorReasonOfResult(positionAfterx0),
      EverParseGetValidatorErrorKind(positionAfterx0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterx = positionAfterx0;
  }
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Validating field y */
  positionAftery = ValidateInt(Ctxt, ErrorHandlerFn, Input, InputLength, positionAfterx);
  if (EverParseIsSuccess(positionAftery))
  {
    return positionAftery;
  }
  ErrorHandlerFn("_POINT",
    "y",
    EverParseErrorReasonOfResult(positionAftery),
    EverParseGetValidatorErrorKind(positionAftery),
    Ctxt,
    Input,
    positionAfterx);
  return positionAftery;
}

