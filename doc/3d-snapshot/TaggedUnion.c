

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

static inline uint64_t ValidateIntPayloadValue32(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _int_payload_value32
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value32 */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      TAGGEDUNION__INT_PAYLOAD__VALUE32);
}

static inline uint64_t ValidateIntPayloadValue16(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _int_payload_value16
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value16 */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)2U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)2U;
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      TAGGEDUNION__INT_PAYLOAD__VALUE16);
}

static inline uint64_t ValidateIntPayloadValue8(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _int_payload_value8
        of type TaggedUnion._int_payload
--*/
{
  /* Validating field value8 */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)1U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)1U;
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      TAGGEDUNION__INT_PAYLOAD__VALUE8);
}

static inline uint64_t
ValidateIntPayload(uint32_t Size, uint32_t InputLength, uint64_t StartPosition)
{
  if (Size == (uint32_t)SIZE8)
  {
    /* Field _int_payload_value8 */
    return ValidateIntPayloadValue8(InputLength, StartPosition);
  }
  if (Size == (uint32_t)SIZE16)
  {
    /* Field _int_payload_value16 */
    return ValidateIntPayloadValue16(InputLength, StartPosition);
  }
  if (Size == (uint32_t)SIZE32)
  {
    /* Field _int_payload_value32 */
    return ValidateIntPayloadValue32(InputLength, StartPosition);
  }
  return EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE;
}

static inline uint64_t ValidateIntegerSize(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _integer_size
        of type TaggedUnion._integer
--*/
{
  /* Validating field size */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)4U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)4U;
  }
  return
    EverParseMaybeSetErrorCode(endPositionOrError,
      StartPosition,
      TAGGEDUNION__INTEGER__SIZE);
}

static inline uint64_t
ValidateIntegerPayload(uint32_t Size, uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _integer_payload
        of type TaggedUnion._integer
--*/
{
  /* Validating field payload */
  return ValidateIntPayload(Size, InputLength, StartPosition);
}

uint64_t
TaggedUnionValidateInteger(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _integer_size */
  uint64_t positionAftersize = ValidateIntegerSize(InputLength, StartPosition);
  if (EverParseIsError(positionAftersize))
  {
    return positionAftersize;
  }
  uint8_t *base = Input;
  uint32_t size = Load32Le(base + (uint32_t)StartPosition);
  /* Field _integer_payload */
  return ValidateIntegerPayload(size, InputLength, positionAftersize);
}

