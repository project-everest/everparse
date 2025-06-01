

#include "TaggedUnion.h"

static inline uint64_t
ValidateIntPayload(
  uint32_t Size,
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
  if (Size == (uint32_t)TAGGEDUNION_SIZE8)
  {
    /* Validating field value8 */
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    BOOLEAN hasBytes = 1ULL <= (InputLen - StartPosition);
    uint64_t positionAfterIntPayload;
    if (hasBytes)
    {
      positionAfterIntPayload = StartPosition + 1ULL;
    }
    else
    {
      positionAfterIntPayload =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterIntPayload))
    {
      return positionAfterIntPayload;
    }
    ErrorHandlerFn("_int_payload",
      "value8",
      EverParseErrorReasonOfResult(positionAfterIntPayload),
      EverParseGetValidatorErrorKind(positionAfterIntPayload),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterIntPayload;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE16)
  {
    /* Validating field value16 */
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    BOOLEAN hasBytes = 2ULL <= (InputLen - StartPosition);
    uint64_t positionAfterIntPayload;
    if (hasBytes)
    {
      positionAfterIntPayload = StartPosition + 2ULL;
    }
    else
    {
      positionAfterIntPayload =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterIntPayload))
    {
      return positionAfterIntPayload;
    }
    ErrorHandlerFn("_int_payload",
      "value16",
      EverParseErrorReasonOfResult(positionAfterIntPayload),
      EverParseGetValidatorErrorKind(positionAfterIntPayload),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterIntPayload;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE32)
  {
    /* Validating field value32 */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    BOOLEAN hasBytes = 4ULL <= (InputLen - StartPosition);
    uint64_t positionAfterIntPayload;
    if (hasBytes)
    {
      positionAfterIntPayload = StartPosition + 4ULL;
    }
    else
    {
      positionAfterIntPayload =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterIntPayload))
    {
      return positionAfterIntPayload;
    }
    ErrorHandlerFn("_int_payload",
      "value32",
      EverParseErrorReasonOfResult(positionAfterIntPayload),
      EverParseGetValidatorErrorKind(positionAfterIntPayload),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterIntPayload;
  }
  uint64_t
  positionAfterIntPayload =
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
      StartPosition);
  if (EverParseIsSuccess(positionAfterIntPayload))
  {
    return positionAfterIntPayload;
  }
  ErrorHandlerFn("_int_payload",
    "_x_17",
    EverParseErrorReasonOfResult(positionAfterIntPayload),
    EverParseGetValidatorErrorKind(positionAfterIntPayload),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterIntPayload;
}

uint64_t
TaggedUnionValidateInteger(
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
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = 4ULL <= (InputLength - StartPosition);
  uint64_t positionAfterInteger;
  if (hasBytes)
  {
    positionAfterInteger = StartPosition + 4ULL;
  }
  else
  {
    positionAfterInteger =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAftersize;
  if (EverParseIsSuccess(positionAfterInteger))
  {
    positionAftersize = positionAfterInteger;
  }
  else
  {
    ErrorHandlerFn("_integer",
      "size",
      EverParseErrorReasonOfResult(positionAfterInteger),
      EverParseGetValidatorErrorKind(positionAfterInteger),
      Ctxt,
      Input,
      StartPosition);
    positionAftersize = positionAfterInteger;
  }
  if (EverParseIsError(positionAftersize))
  {
    return positionAftersize;
  }
  uint32_t size = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field payload */
  uint64_t
  positionAfterInteger0 =
    ValidateIntPayload(size,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAftersize);
  if (EverParseIsSuccess(positionAfterInteger0))
  {
    return positionAfterInteger0;
  }
  ErrorHandlerFn("_integer",
    "payload",
    EverParseErrorReasonOfResult(positionAfterInteger0),
    EverParseGetValidatorErrorKind(positionAfterInteger0),
    Ctxt,
    Input,
    positionAftersize);
  return positionAfterInteger0;
}

