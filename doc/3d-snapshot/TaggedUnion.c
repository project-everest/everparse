

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
  BOOLEAN hasBytesForValue8;
  uint64_t positionAfterValue8OrError;
  BOOLEAN hasBytesForValue16;
  uint64_t positionAfterValue16OrError;
  BOOLEAN hasBytesForValue32;
  uint64_t positionAfterValue32OrError;
  uint64_t positionAfterX17orError;
  if (Size == (uint32_t)TAGGEDUNION_SIZE8)
  {
    /* Validating field value8 */
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    hasBytesForValue8 = (InputLen - StartPosition) >= 1ULL;
    if (hasBytesForValue8)
    {
      positionAfterValue8OrError = StartPosition + 1ULL;
    }
    else
    {
      positionAfterValue8OrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterValue8OrError))
    {
      return positionAfterValue8OrError;
    }
    ErrorHandlerFn("_int_payload",
      "value8",
      EverParseErrorReasonOfResult(positionAfterValue8OrError),
      EverParseGetValidatorErrorKind(positionAfterValue8OrError),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterValue8OrError;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE16)
  {
    /* Validating field value16 */
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    hasBytesForValue16 = (InputLen - StartPosition) >= 2ULL;
    if (hasBytesForValue16)
    {
      positionAfterValue16OrError = StartPosition + 2ULL;
    }
    else
    {
      positionAfterValue16OrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterValue16OrError))
    {
      return positionAfterValue16OrError;
    }
    ErrorHandlerFn("_int_payload",
      "value16",
      EverParseErrorReasonOfResult(positionAfterValue16OrError),
      EverParseGetValidatorErrorKind(positionAfterValue16OrError),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterValue16OrError;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE32)
  {
    /* Validating field value32 */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    hasBytesForValue32 = (InputLen - StartPosition) >= 4ULL;
    if (hasBytesForValue32)
    {
      positionAfterValue32OrError = StartPosition + 4ULL;
    }
    else
    {
      positionAfterValue32OrError =
        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
          StartPosition);
    }
    if (EverParseIsSuccess(positionAfterValue32OrError))
    {
      return positionAfterValue32OrError;
    }
    ErrorHandlerFn("_int_payload",
      "value32",
      EverParseErrorReasonOfResult(positionAfterValue32OrError),
      EverParseGetValidatorErrorKind(positionAfterValue32OrError),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterValue32OrError;
  }
  positionAfterX17orError =
    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
      StartPosition);
  if (EverParseIsSuccess(positionAfterX17orError))
  {
    return positionAfterX17orError;
  }
  ErrorHandlerFn("_int_payload",
    "_x_17",
    EverParseErrorReasonOfResult(positionAfterX17orError),
    EverParseGetValidatorErrorKind(positionAfterX17orError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterX17orError;
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
  BOOLEAN hasBytesForSize = (InputLength - StartPosition) >= 4ULL;
  uint64_t positionAfterSizeOrError;
  uint64_t positionAfterSize;
  uint32_t size;
  uint64_t positionAfterPayloadOrError;
  if (hasBytesForSize)
  {
    positionAfterSizeOrError = StartPosition + 4ULL;
  }
  else
  {
    positionAfterSizeOrError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterSizeOrError))
  {
    positionAfterSize = positionAfterSizeOrError;
  }
  else
  {
    ErrorHandlerFn("_integer",
      "size",
      EverParseErrorReasonOfResult(positionAfterSizeOrError),
      EverParseGetValidatorErrorKind(positionAfterSizeOrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterSize = positionAfterSizeOrError;
  }
  if (EverParseIsError(positionAfterSize))
  {
    return positionAfterSize;
  }
  size = Load32Le(Input + (uint32_t)StartPosition);
  /* Validating field payload */
  positionAfterPayloadOrError =
    ValidateIntPayload(size,
      Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAfterSize);
  if (EverParseIsSuccess(positionAfterPayloadOrError))
  {
    return positionAfterPayloadOrError;
  }
  ErrorHandlerFn("_integer",
    "payload",
    EverParseErrorReasonOfResult(positionAfterPayloadOrError),
    EverParseGetValidatorErrorKind(positionAfterPayloadOrError),
    Ctxt,
    Input,
    positionAfterSize);
  return positionAfterPayloadOrError;
}

