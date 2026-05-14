

#include "TaggedUnion.h"

#include "EverParse.h"

static inline uint64_t
ValidateIntPayload(
  uint32_t Size,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes0;
  uint64_t positionAfterIntPayload;
  BOOLEAN hasBytes1;
  uint64_t positionAfterIntPayload0;
  BOOLEAN hasBytes;
  uint64_t positionAfterIntPayload1;
  uint64_t positionAfterIntPayload2;
  if (Size == (uint32_t)TAGGEDUNION_SIZE8)
  {
    /* Validating field value8 */
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    hasBytes0 = (InputLen - StartPosition) >= 1ULL;
    if (hasBytes0)
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
    hasBytes1 = (InputLen - StartPosition) >= 2ULL;
    if (hasBytes1)
    {
      positionAfterIntPayload0 = StartPosition + 2ULL;
    }
    else
    {
      positionAfterIntPayload0 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterIntPayload0))
    {
      return positionAfterIntPayload0;
    }
    ErrorHandlerFn("_int_payload",
      "value16",
      EverParseErrorReasonOfResult(positionAfterIntPayload0),
      EverParseGetValidatorErrorKind(positionAfterIntPayload0),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterIntPayload0;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE32)
  {
    /* Validating field value32 */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    hasBytes = (InputLen - StartPosition) >= 4ULL;
    if (hasBytes)
    {
      positionAfterIntPayload1 = StartPosition + 4ULL;
    }
    else
    {
      positionAfterIntPayload1 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterIntPayload1))
    {
      return positionAfterIntPayload1;
    }
    ErrorHandlerFn("_int_payload",
      "value32",
      EverParseErrorReasonOfResult(positionAfterIntPayload1),
      EverParseGetValidatorErrorKind(positionAfterIntPayload1),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterIntPayload1;
  }
  positionAfterIntPayload2 =
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
      StartPosition);
  if (EverParseIsSuccess(positionAfterIntPayload2))
  {
    return positionAfterIntPayload2;
  }
  ErrorHandlerFn("_int_payload",
    "_x_17",
    EverParseErrorReasonOfResult(positionAfterIntPayload2),
    EverParseGetValidatorErrorKind(positionAfterIntPayload2),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterIntPayload2;
}

uint64_t
TaggedUnionValidateInteger(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterInteger;
  uint64_t positionAftersize;
  uint32_t size;
  uint64_t positionAfterInteger0;
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
  size = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field payload */
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

