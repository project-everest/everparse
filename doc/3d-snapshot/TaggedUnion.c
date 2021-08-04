

#include "TaggedUnion.h"

#define SIZE8 ((uint8_t)8U)

#define SIZE16 ((uint8_t)16U)

#define SIZE32 ((uint8_t)32U)

static inline uint64_t
ValidateIntPayloadValue32(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _int_payload_value32
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value32 */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)(uint32_t)4U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterIntPayload;
  if (hasBytes)
  {
    positionAfterIntPayload = Pos + (uint64_t)(uint32_t)4U;
  }
  else
  {
    positionAfterIntPayload =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterIntPayload))
  {
    return positionAfterIntPayload;
  }
  Err("_int_payload",
    "_int_payload_value32",
    EverParseErrorReasonOfResult(positionAfterIntPayload),
    Ctxt,
    Input,
    Pos);
  return positionAfterIntPayload;
}

static inline uint64_t
ValidateIntPayloadValue16(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _int_payload_value16
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value16 */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes = (uint64_t)(uint32_t)2U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterIntPayload;
  if (hasBytes)
  {
    positionAfterIntPayload = Pos + (uint64_t)(uint32_t)2U;
  }
  else
  {
    positionAfterIntPayload =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterIntPayload))
  {
    return positionAfterIntPayload;
  }
  Err("_int_payload",
    "_int_payload_value16",
    EverParseErrorReasonOfResult(positionAfterIntPayload),
    Ctxt,
    Input,
    Pos);
  return positionAfterIntPayload;
}

static inline uint64_t
ValidateIntPayloadValue8(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _int_payload_value8
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value8 */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint64_t)(uint32_t)1U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterIntPayload;
  if (hasBytes)
  {
    positionAfterIntPayload = Pos + (uint64_t)(uint32_t)1U;
  }
  else
  {
    positionAfterIntPayload =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterIntPayload))
  {
    return positionAfterIntPayload;
  }
  Err("_int_payload",
    "_int_payload_value8",
    EverParseErrorReasonOfResult(positionAfterIntPayload),
    Ctxt,
    Input,
    Pos);
  return positionAfterIntPayload;
}

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
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos0
)
{
  uint64_t positionAfterIntPayload;
  if (Size == (uint32_t)SIZE8)
  {
    /* Field _int_payload_value8 */
    uint64_t positionAfterIntPayload0 = ValidateIntPayloadValue8(Ctxt, Err, Input, Pos0);
    uint64_t res;
    if (EverParseIsSuccess(positionAfterIntPayload0))
    {
      res = positionAfterIntPayload0;
    }
    else
    {
      Err("_int_payload",
        "_int_payload_ite_2",
        EverParseErrorReasonOfResult(positionAfterIntPayload0),
        Ctxt,
        Input,
        Pos0);
      res = positionAfterIntPayload0;
    }
    positionAfterIntPayload = res;
  }
  else
  {
    uint64_t positionAfterIntPayload0;
    if (Size == (uint32_t)SIZE16)
    {
      /* Field _int_payload_value16 */
      uint64_t positionAfterIntPayload = ValidateIntPayloadValue16(Ctxt, Err, Input, Pos0);
      uint64_t res;
      if (EverParseIsSuccess(positionAfterIntPayload))
      {
        res = positionAfterIntPayload;
      }
      else
      {
        Err("_int_payload",
          "_int_payload_ite_1",
          EverParseErrorReasonOfResult(positionAfterIntPayload),
          Ctxt,
          Input,
          Pos0);
        res = positionAfterIntPayload;
      }
      positionAfterIntPayload0 = res;
    }
    else
    {
      uint64_t positionAfterIntPayload;
      if (Size == (uint32_t)SIZE32)
      {
        /* Field _int_payload_value32 */
        uint64_t positionAfterIntPayload0 = ValidateIntPayloadValue32(Ctxt, Err, Input, Pos0);
        uint64_t res;
        if (EverParseIsSuccess(positionAfterIntPayload0))
        {
          res = positionAfterIntPayload0;
        }
        else
        {
          Err("_int_payload",
            "_int_payload_ite_0",
            EverParseErrorReasonOfResult(positionAfterIntPayload0),
            Ctxt,
            Input,
            Pos0);
          res = positionAfterIntPayload0;
        }
        positionAfterIntPayload = res;
      }
      else
      {
        uint64_t
        positionAfterIntPayload0 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE,
            Pos0);
        uint64_t res;
        if (EverParseIsSuccess(positionAfterIntPayload0))
        {
          res = positionAfterIntPayload0;
        }
        else
        {
          Err("_int_payload",
            "_int_payload_ite_0",
            EverParseErrorReasonOfResult(positionAfterIntPayload0),
            Ctxt,
            Input,
            Pos0);
          res = positionAfterIntPayload0;
        }
        positionAfterIntPayload = res;
      }
      if (EverParseIsSuccess(positionAfterIntPayload))
      {
        positionAfterIntPayload0 = positionAfterIntPayload;
      }
      else
      {
        Err("_int_payload",
          "_int_payload_ite_1",
          EverParseErrorReasonOfResult(positionAfterIntPayload),
          Ctxt,
          Input,
          Pos0);
        positionAfterIntPayload0 = positionAfterIntPayload;
      }
    }
    if (EverParseIsSuccess(positionAfterIntPayload0))
    {
      positionAfterIntPayload = positionAfterIntPayload0;
    }
    else
    {
      Err("_int_payload",
        "_int_payload_ite_2",
        EverParseErrorReasonOfResult(positionAfterIntPayload0),
        Ctxt,
        Input,
        Pos0);
      positionAfterIntPayload = positionAfterIntPayload0;
    }
  }
  if (EverParseIsSuccess(positionAfterIntPayload))
  {
    return positionAfterIntPayload;
  }
  Err("_int_payload",
    "",
    EverParseErrorReasonOfResult(positionAfterIntPayload),
    Ctxt,
    Input,
    Pos0);
  return positionAfterIntPayload;
}

static inline uint64_t
ValidateIntegerSize(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _integer_size
        of type TaggedUnion._integer
--*/
{
  /* Validating field size */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)(uint32_t)4U <= ((uint64_t)Input.len - Pos);
  uint64_t positionAfterInteger;
  if (hasBytes)
  {
    positionAfterInteger = Pos + (uint64_t)(uint32_t)4U;
  }
  else
  {
    positionAfterInteger =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        Pos);
  }
  if (EverParseIsSuccess(positionAfterInteger))
  {
    return positionAfterInteger;
  }
  Err("_integer",
    "_integer_size",
    EverParseErrorReasonOfResult(positionAfterInteger),
    Ctxt,
    Input,
    Pos);
  return positionAfterInteger;
}

static inline uint64_t
ValidateIntegerPayload(
  uint32_t Size,
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _integer_payload
        of type TaggedUnion._integer
--*/
{
  /* Validating field payload */
  uint64_t positionAfterInteger = ValidateIntPayload(Size, Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterInteger))
  {
    return positionAfterInteger;
  }
  Err("_integer",
    "_integer_payload",
    EverParseErrorReasonOfResult(positionAfterInteger),
    Ctxt,
    Input,
    Pos);
  return positionAfterInteger;
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
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
{
  /* Field _integer_size */
  uint64_t positionAfterInteger = ValidateIntegerSize(Ctxt, Err, Input, Pos);
  uint64_t positionAftersize;
  if (EverParseIsSuccess(positionAfterInteger))
  {
    positionAftersize = positionAfterInteger;
  }
  else
  {
    Err("_integer", "size", EverParseErrorReasonOfResult(positionAfterInteger), Ctxt, Input, Pos);
    positionAftersize = positionAfterInteger;
  }
  if (EverParseIsError(positionAftersize))
  {
    return positionAftersize;
  }
  uint8_t temp[4U] = { 0U };
  uint8_t *temp1 = Input.buf + (uint32_t)Pos;
  uint32_t res = Load32Le(temp1);
  uint32_t size = res;
  /* Field _integer_payload */
  uint64_t
  positionAfterInteger0 = ValidateIntegerPayload(size, Ctxt, Err, Input, positionAftersize);
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

