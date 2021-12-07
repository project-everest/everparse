

#include "TaggedUnion.h"

static inline uint64_t
ValidateIntPayload(
  uint32_t Size,
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
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
    BOOLEAN hasBytes = (uint64_t)1U <= (InputLen - StartPosition);
    uint64_t positionAfterIntPayload;
    if (hasBytes)
    {
      positionAfterIntPayload = StartPosition + (uint64_t)1U;
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
    Err("_int_payload",
      "missing",
      EverParseErrorReasonOfResult(positionAfterIntPayload),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterIntPayload;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE16)
  {
    /* Validating field value16 */
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    BOOLEAN hasBytes = (uint64_t)2U <= (InputLen - StartPosition);
    uint64_t positionAfterIntPayload;
    if (hasBytes)
    {
      positionAfterIntPayload = StartPosition + (uint64_t)2U;
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
    Err("_int_payload",
      "missing",
      EverParseErrorReasonOfResult(positionAfterIntPayload),
      Ctxt,
      Input,
      StartPosition);
    return positionAfterIntPayload;
  }
  if (Size == (uint32_t)TAGGEDUNION_SIZE32)
  {
    /* Validating field value32 */
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    BOOLEAN hasBytes = (uint64_t)4U <= (InputLen - StartPosition);
    uint64_t positionAfterIntPayload;
    if (hasBytes)
    {
      positionAfterIntPayload = StartPosition + (uint64_t)4U;
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
    Err("_int_payload",
      "missing",
      EverParseErrorReasonOfResult(positionAfterIntPayload),
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
  Err("_int_payload",
    "missing",
    EverParseErrorReasonOfResult(positionAfterIntPayload),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterIntPayload;
}

uint64_t
TaggedUnionValidateInteger(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterInteger;
  if (hasBytes)
  {
    positionAfterInteger = StartPosition + (uint64_t)4U;
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
    Err("_integer",
      "size",
      EverParseErrorReasonOfResult(positionAfterInteger),
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
      Err,
      Input,
      InputLength,
      positionAftersize);
  if (EverParseIsSuccess(positionAfterInteger0))
  {
    return positionAfterInteger0;
  }
  Err("_integer",
    "payload",
    EverParseErrorReasonOfResult(positionAfterInteger0),
    Ctxt,
    Input,
    positionAftersize);
  return positionAfterInteger0;
}

