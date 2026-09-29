

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
  uint64_t positionAftervalue8;
  BOOLEAN hasBytes1;
  uint64_t positionAftervalue16;
  BOOLEAN hasBytes;
  uint64_t positionAftervalue32;
  uint64_t positionAfterX17;
  if (Size == (uint32_t)TAGGEDUNION_SIZE8)
  {
    /* Validating field value8 */
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    hasBytes0 = (InputLen - StartPosition) >= 1ULL;
    if (hasBytes0)
    {
      positionAftervalue8 = StartPosition + 1ULL;
    }
    else
    {
      positionAftervalue8 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAftervalue8))
    {
      return positionAftervalue8;
    }
    ErrorHandlerFn("_int_payload",
      "value8",
      EverParseErrorReasonOfResult(positionAftervalue8),
      EverParseGetValidatorErrorKind(positionAftervalue8),
      Ctxt,
      Input,
      StartPosition);
    return positionAftervalue8;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE16)
  {
    /* Validating field value16 */
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    hasBytes1 = (InputLen - StartPosition) >= 2ULL;
    if (hasBytes1)
    {
      positionAftervalue16 = StartPosition + 2ULL;
    }
    else
    {
      positionAftervalue16 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAftervalue16))
    {
      return positionAftervalue16;
    }
    ErrorHandlerFn("_int_payload",
      "value16",
      EverParseErrorReasonOfResult(positionAftervalue16),
      EverParseGetValidatorErrorKind(positionAftervalue16),
      Ctxt,
      Input,
      StartPosition);
    return positionAftervalue16;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE32)
  {
    /* Validating field value32 */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    hasBytes = (InputLen - StartPosition) >= 4ULL;
    if (hasBytes)
    {
      positionAftervalue32 = StartPosition + 4ULL;
    }
    else
    {
      positionAftervalue32 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAftervalue32))
    {
      return positionAftervalue32;
    }
    ErrorHandlerFn("_int_payload",
      "value32",
      EverParseErrorReasonOfResult(positionAftervalue32),
      EverParseGetValidatorErrorKind(positionAftervalue32),
      Ctxt,
      Input,
      StartPosition);
    return positionAftervalue32;
  }
  positionAfterX17 =
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
      StartPosition);
  if (EverParseIsSuccess(positionAfterX17))
  {
    return positionAfterX17;
  }
  ErrorHandlerFn("_int_payload",
    "_x_17",
    EverParseErrorReasonOfResult(positionAfterX17),
    EverParseGetValidatorErrorKind(positionAfterX17),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX17;
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
  uint64_t positionAftersize0;
  uint64_t positionAftersize;
  uint32_t size;
  uint64_t positionAfterpayload;
  if (hasBytes)
  {
    positionAftersize0 = StartPosition + 4ULL;
  }
  else
  {
    positionAftersize0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAftersize0))
  {
    positionAftersize = positionAftersize0;
  }
  else
  {
    ErrorHandlerFn("_integer",
      "size",
      EverParseErrorReasonOfResult(positionAftersize0),
      EverParseGetValidatorErrorKind(positionAftersize0),
      Ctxt,
      Input,
      StartPosition);
    positionAftersize = positionAftersize0;
  }
  if (EverParseIsError(positionAftersize))
  {
    return positionAftersize;
  }
  size = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field payload */
  positionAfterpayload =
    ValidateIntPayload(size,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAftersize);
  if (EverParseIsSuccess(positionAfterpayload))
  {
    return positionAfterpayload;
  }
  ErrorHandlerFn("_integer",
    "payload",
    EverParseErrorReasonOfResult(positionAfterpayload),
    EverParseGetValidatorErrorKind(positionAfterpayload),
    Ctxt,
    Input,
    positionAftersize);
  return positionAfterpayload;
}

