

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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _int_payload_value32
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value32 */
  uint32_t positionBeforeIntPayload = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterIntPayload;
  if (hasBytes)
  {
    resultAfterIntPayload = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterIntPayload = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterIntPayload))
  {
    return resultAfterIntPayload;
  }
  Err("_int_payload",
    "_int_payload_value32",
    EverParseErrorReasonOfResult(resultAfterIntPayload),
    Ctxt,
    Input,
    positionBeforeIntPayload);
  return resultAfterIntPayload;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _int_payload_value16
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value16 */
  uint32_t positionBeforeIntPayload = *Input.pos;
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - currentPosition);
  uint64_t resultAfterIntPayload;
  if (hasBytes)
  {
    resultAfterIntPayload = (uint64_t)(uint32_t)2U;
  }
  else
  {
    resultAfterIntPayload = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterIntPayload))
  {
    return resultAfterIntPayload;
  }
  Err("_int_payload",
    "_int_payload_value16",
    EverParseErrorReasonOfResult(resultAfterIntPayload),
    Ctxt,
    Input,
    positionBeforeIntPayload);
  return resultAfterIntPayload;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _int_payload_value8
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value8 */
  uint32_t positionBeforeIntPayload = *Input.pos;
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - currentPosition);
  uint64_t resultAfterIntPayload;
  if (hasBytes)
  {
    resultAfterIntPayload = (uint64_t)(uint32_t)1U;
  }
  else
  {
    resultAfterIntPayload = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterIntPayload))
  {
    return resultAfterIntPayload;
  }
  Err("_int_payload",
    "_int_payload_value8",
    EverParseErrorReasonOfResult(resultAfterIntPayload),
    Ctxt,
    Input,
    positionBeforeIntPayload);
  return resultAfterIntPayload;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
{
  uint32_t positionBeforeIntPayload = *Input.pos;
  uint64_t resultAfterIntPayload;
  if (Size == (uint32_t)SIZE8)
  {
    /* Field _int_payload_value8 */
    uint32_t positionBeforeIntPayload1 = *Input.pos;
    uint64_t resultAfterIntPayload0 = ValidateIntPayloadValue8(Ctxt, Err, Input);
    uint64_t res;
    if (EverParseIsSuccess(resultAfterIntPayload0))
    {
      res = resultAfterIntPayload0;
    }
    else
    {
      Err("_int_payload",
        "_int_payload_ite_2",
        EverParseErrorReasonOfResult(resultAfterIntPayload0),
        Ctxt,
        Input,
        positionBeforeIntPayload1);
      res = resultAfterIntPayload0;
    }
    if (EverParseIsSuccess(res))
    {
      uint32_t currentPosition = *Input.pos;
      *Input.pos = currentPosition + (uint32_t)res;
    }
    resultAfterIntPayload = res;
  }
  else
  {
    uint32_t positionBeforeIntPayload1 = *Input.pos;
    uint64_t resultAfterIntPayload0;
    if (Size == (uint32_t)SIZE16)
    {
      /* Field _int_payload_value16 */
      uint32_t positionBeforeIntPayload2 = *Input.pos;
      uint64_t resultAfterIntPayload = ValidateIntPayloadValue16(Ctxt, Err, Input);
      uint64_t res;
      if (EverParseIsSuccess(resultAfterIntPayload))
      {
        res = resultAfterIntPayload;
      }
      else
      {
        Err("_int_payload",
          "_int_payload_ite_1",
          EverParseErrorReasonOfResult(resultAfterIntPayload),
          Ctxt,
          Input,
          positionBeforeIntPayload2);
        res = resultAfterIntPayload;
      }
      if (EverParseIsSuccess(res))
      {
        uint32_t currentPosition = *Input.pos;
        *Input.pos = currentPosition + (uint32_t)res;
      }
      resultAfterIntPayload0 = res;
    }
    else
    {
      uint32_t positionBeforeIntPayload2 = *Input.pos;
      uint64_t resultAfterIntPayload;
      if (Size == (uint32_t)SIZE32)
      {
        /* Field _int_payload_value32 */
        uint32_t positionBeforeIntPayload3 = *Input.pos;
        uint64_t resultAfterIntPayload0 = ValidateIntPayloadValue32(Ctxt, Err, Input);
        uint64_t res;
        if (EverParseIsSuccess(resultAfterIntPayload0))
        {
          res = resultAfterIntPayload0;
        }
        else
        {
          Err("_int_payload",
            "_int_payload_ite_0",
            EverParseErrorReasonOfResult(resultAfterIntPayload0),
            Ctxt,
            Input,
            positionBeforeIntPayload3);
          res = resultAfterIntPayload0;
        }
        if (EverParseIsSuccess(res))
        {
          uint32_t currentPosition = *Input.pos;
          *Input.pos = currentPosition + (uint32_t)res;
        }
        resultAfterIntPayload = res;
      }
      else
      {
        uint32_t positionBeforeIntPayload3 = *Input.pos;
        uint64_t resultAfterIntPayload0 = EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE;
        uint64_t res;
        if (EverParseIsSuccess(resultAfterIntPayload0))
        {
          res = resultAfterIntPayload0;
        }
        else
        {
          Err("_int_payload",
            "_int_payload_ite_0",
            EverParseErrorReasonOfResult(resultAfterIntPayload0),
            Ctxt,
            Input,
            positionBeforeIntPayload3);
          res = resultAfterIntPayload0;
        }
        if (EverParseIsSuccess(res))
        {
          uint32_t currentPosition = *Input.pos;
          *Input.pos = currentPosition + (uint32_t)res;
        }
        resultAfterIntPayload = res;
      }
      if (EverParseIsSuccess(resultAfterIntPayload))
      {
        resultAfterIntPayload0 = resultAfterIntPayload;
      }
      else
      {
        Err("_int_payload",
          "_int_payload_ite_1",
          EverParseErrorReasonOfResult(resultAfterIntPayload),
          Ctxt,
          Input,
          positionBeforeIntPayload2);
        resultAfterIntPayload0 = resultAfterIntPayload;
      }
    }
    if (EverParseIsSuccess(resultAfterIntPayload0))
    {
      resultAfterIntPayload = resultAfterIntPayload0;
    }
    else
    {
      Err("_int_payload",
        "_int_payload_ite_2",
        EverParseErrorReasonOfResult(resultAfterIntPayload0),
        Ctxt,
        Input,
        positionBeforeIntPayload1);
      resultAfterIntPayload = resultAfterIntPayload0;
    }
  }
  if (EverParseIsSuccess(resultAfterIntPayload))
  {
    return resultAfterIntPayload;
  }
  Err("_int_payload",
    "",
    EverParseErrorReasonOfResult(resultAfterIntPayload),
    Ctxt,
    Input,
    positionBeforeIntPayload);
  return resultAfterIntPayload;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _integer_size
        of type TaggedUnion._integer
--*/
{
  /* Validating field size */
  uint32_t positionBeforeInteger = *Input.pos;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t resultAfterInteger;
  if (hasBytes)
  {
    resultAfterInteger = (uint64_t)(uint32_t)4U;
  }
  else
  {
    resultAfterInteger = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(resultAfterInteger))
  {
    return resultAfterInteger;
  }
  Err("_integer",
    "_integer_size",
    EverParseErrorReasonOfResult(resultAfterInteger),
    Ctxt,
    Input,
    positionBeforeInteger);
  return resultAfterInteger;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _integer_payload
        of type TaggedUnion._integer
--*/
{
  /* Validating field payload */
  uint32_t positionBeforeInteger = *Input.pos;
  uint64_t resultAfterInteger = ValidateIntPayload(Size, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterInteger))
  {
    return resultAfterInteger;
  }
  Err("_integer",
    "_integer_payload",
    EverParseErrorReasonOfResult(resultAfterInteger),
    Ctxt,
    Input,
    positionBeforeInteger);
  return resultAfterInteger;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
{
  /* Field _integer_size */
  uint32_t positionBeforeInteger = *Input.pos;
  uint64_t resultAfterInteger = ValidateIntegerSize(Ctxt, Err, Input);
  uint64_t resultAftersize;
  if (EverParseIsSuccess(resultAfterInteger))
  {
    resultAftersize = resultAfterInteger;
  }
  else
  {
    Err("_integer",
      "size",
      EverParseErrorReasonOfResult(resultAfterInteger),
      Ctxt,
      Input,
      positionBeforeInteger);
    resultAftersize = resultAfterInteger;
  }
  if (EverParseIsError(resultAftersize))
  {
    return resultAftersize;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition = *Input.pos;
  uint8_t *res = Input.buf + currentPosition;
  *Input.pos = currentPosition + (uint32_t)4U;
  uint8_t *temp1 = res;
  uint32_t res0 = Load32Le(temp1);
  uint32_t size = res0;
  /* Field _integer_payload */
  uint32_t positionBeforeInteger0 = *Input.pos;
  uint64_t resultAfterInteger0 = ValidateIntegerPayload(size, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterInteger0))
  {
    return resultAfterInteger0;
  }
  Err("_integer",
    "payload",
    EverParseErrorReasonOfResult(resultAfterInteger0),
    Ctxt,
    Input,
    positionBeforeInteger0);
  return resultAfterInteger0;
}

