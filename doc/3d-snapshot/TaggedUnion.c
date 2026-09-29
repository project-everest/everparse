

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
  uint64_t positionAfterValue8;
  BOOLEAN hasBytes1;
  uint64_t positionAfterValue16;
  BOOLEAN hasBytes;
  uint64_t positionAfterValue32;
  uint64_t positionAfterX17;
  if (Size == (uint32_t)TAGGEDUNION_SIZE8)
  {
    /* Validating field value8 */
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    hasBytes0 = (InputLen - StartPosition) >= 1ULL;
    if (hasBytes0)
    {
      positionAfterValue8 = StartPosition + 1ULL;
    }
    else
    {
      positionAfterValue8 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterValue8))
    {
      return positionAfterValue8;
    }
    ErrorHandlerFn("_int_payload",
      "value8",
      EverParseErrorReasonOfResult(positionAfterValue8),
      EverParseGetValidatorErrorKind(positionAfterValue8),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterValue8;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE16)
  {
    /* Validating field value16 */
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    hasBytes1 = (InputLen - StartPosition) >= 2ULL;
    if (hasBytes1)
    {
      positionAfterValue16 = StartPosition + 2ULL;
    }
    else
    {
      positionAfterValue16 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterValue16))
    {
      return positionAfterValue16;
    }
    ErrorHandlerFn("_int_payload",
      "value16",
      EverParseErrorReasonOfResult(positionAfterValue16),
      EverParseGetValidatorErrorKind(positionAfterValue16),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterValue16;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE32)
  {
    /* Validating field value32 */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    hasBytes = (InputLen - StartPosition) >= 4ULL;
    if (hasBytes)
    {
      positionAfterValue32 = StartPosition + 4ULL;
    }
    else
    {
      positionAfterValue32 =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterValue32))
    {
      return positionAfterValue32;
    }
    ErrorHandlerFn("_int_payload",
      "value32",
      EverParseErrorReasonOfResult(positionAfterValue32),
      EverParseGetValidatorErrorKind(positionAfterValue32),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterValue32;
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
  uint64_t positionAfterSize0;
  uint64_t positionAfterSize;
  uint32_t size;
  uint64_t positionAfterPayload;
  if (hasBytes)
  {
    positionAfterSize0 = StartPosition + 4ULL;
  }
  else
  {
    positionAfterSize0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterSize0))
  {
    positionAfterSize = positionAfterSize0;
  }
  else
  {
    ErrorHandlerFn("_integer",
      "size",
      EverParseErrorReasonOfResult(positionAfterSize0),
      EverParseGetValidatorErrorKind(positionAfterSize0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterSize = positionAfterSize0;
  }
  if (EverParseIsError(positionAfterSize))
  {
    return positionAfterSize;
  }
  size = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field payload */
  positionAfterPayload =
    ValidateIntPayload(size,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAfterSize);
  if (EverParseIsSuccess(positionAfterPayload))
  {
    return positionAfterPayload;
  }
  ErrorHandlerFn("_integer",
    "payload",
    EverParseErrorReasonOfResult(positionAfterPayload),
    EverParseGetValidatorErrorKind(positionAfterPayload),
    Ctxt,
    Input,
    positionAfterSize);
  return positionAfterPayload;
}

