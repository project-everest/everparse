

#include "TaggedUnion.h"

/*
Auto-generated field identifier for error reporting
*/
#define TAGGEDUNION__INT_PAYLOAD__VALUE8 ((uint64_t)39U)

/*
Auto-generated field identifier for error reporting
*/
#define TAGGEDUNION__INT_PAYLOAD__VALUE16 ((uint64_t)40U)

/*
Auto-generated field identifier for error reporting
*/
#define TAGGEDUNION__INT_PAYLOAD__VALUE32 ((uint64_t)41U)

/*
Auto-generated field identifier for error reporting
*/
#define TAGGEDUNION__INTEGER__SIZE ((uint64_t)42U)

#define SIZE8 ((uint8_t)8U)

#define SIZE16 ((uint8_t)16U)

#define SIZE32 ((uint8_t)32U)

static inline uint64_t ValidateIntPayloadValue32(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _int_payload_value32
        of type TaggedUnion._int_payload
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field value32 */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, TAGGEDUNION__INT_PAYLOAD__VALUE32);
}

static inline uint64_t ValidateIntPayloadValue16(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _int_payload_value16
        of type TaggedUnion._int_payload
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field value16 */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)2U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)2U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, TAGGEDUNION__INT_PAYLOAD__VALUE16);
}

static inline uint64_t ValidateIntPayloadValue8(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _int_payload_value8
        of type TaggedUnion._int_payload
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field value8 */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)1U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)1U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, TAGGEDUNION__INT_PAYLOAD__VALUE8);
}

static inline uint64_t ValidateIntPayload(uint32_t Size, EverParseInputBuffer Sl)
{
  if (Size == (uint32_t)SIZE8)
  {
    /* Field _int_payload_value8 */
    uint64_t res = ValidateIntPayloadValue8(Sl);
    if (EverParseIsSuccess(res))
    {
      uint32_t currentPosition = *Sl.pos;
      *Sl.pos = currentPosition + (uint32_t)res;
    }
    return res;
  }
  if (Size == (uint32_t)SIZE16)
  {
    /* Field _int_payload_value16 */
    uint64_t res = ValidateIntPayloadValue16(Sl);
    if (EverParseIsSuccess(res))
    {
      uint32_t currentPosition = *Sl.pos;
      *Sl.pos = currentPosition + (uint32_t)res;
    }
    return res;
  }
  if (Size == (uint32_t)SIZE32)
  {
    /* Field _int_payload_value32 */
    uint64_t res = ValidateIntPayloadValue32(Sl);
    if (EverParseIsSuccess(res))
    {
      uint32_t currentPosition = *Sl.pos;
      *Sl.pos = currentPosition + (uint32_t)res;
    }
    return res;
  }
  uint64_t res = EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE;
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Sl.pos;
    *Sl.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

static inline uint64_t ValidateIntegerSize(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _integer_size
        of type TaggedUnion._integer
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field size */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  uint32_t currentPosition = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)4U <= (Input.len - currentPosition);
  uint64_t result;
  if (hasBytes)
  {
    result = (uint64_t)(uint32_t)4U;
  }
  else
  {
    result = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, TAGGEDUNION__INTEGER__SIZE);
}

static inline uint64_t ValidateIntegerPayload(uint32_t Size, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _integer_payload
        of type TaggedUnion._integer
--*/
{
  /* Validating field payload */
  return ValidateIntPayload(Size, Input);
}

uint64_t TaggedUnionValidateInteger(EverParseInputBuffer Input)
{
  /* Field _integer_size */
  uint64_t resultAftersize = ValidateIntegerSize(Input);
  if (EverParseIsError(resultAftersize))
  {
    return resultAftersize;
  }
  uint8_t temp[4U] = { 0U };
  uint32_t currentPosition = *Input.pos;
  memcpy(temp, Input.buf + currentPosition, (uint32_t)4U * sizeof (uint8_t));
  *Input.pos = currentPosition + (uint32_t)4U;
  uint32_t res = Load32Le(temp);
  uint32_t size = res;
  /* Field _integer_payload */
  return ValidateIntegerPayload(size, Input);
}

