

#include "BF.h"

static inline uint64_t
ValidateBf2bis(
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
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength - StartPosition);
  uint64_t positionAfterBf2bis;
  if (hasBytes0)
  {
    positionAfterBf2bis = StartPosition + 2ULL;
  }
  else
  {
    positionAfterBf2bis =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterBitfield0;
  if (EverParseIsSuccess(positionAfterBf2bis))
  {
    positionAfterBitfield0 = positionAfterBf2bis;
  }
  else
  {
    ErrorHandlerFn("_BF2bis",
      "__bitfield_0",
      EverParseErrorReasonOfResult(positionAfterBf2bis),
      EverParseGetValidatorErrorKind(positionAfterBf2bis),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBitfield0 = positionAfterBf2bis;
  }
  if (EverParseIsError(positionAfterBitfield0))
  {
    return positionAfterBitfield0;
  }
  uint16_t r0 = Load16Le(Input + (uint32_t)StartPosition);
  uint16_t bitfield0 = (uint16_t)(uint32_t)r0;
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength - positionAfterBitfield0);
  uint64_t positionAfterBitfield1;
  if (hasBytes1)
  {
    positionAfterBitfield1 = positionAfterBitfield0 + 2ULL;
  }
  else
  {
    positionAfterBitfield1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBitfield0);
  }
  uint64_t positionAfterBf2bis0;
  if (EverParseIsError(positionAfterBitfield1))
  {
    positionAfterBf2bis0 = positionAfterBitfield1;
  }
  else
  {
    uint16_t r = Load16Le(Input + (uint32_t)positionAfterBitfield0);
    uint16_t bitfield1 = (uint16_t)(uint32_t)r;
    BOOLEAN
    bitfield1constraintIsOk =
      EverParseGetBitfield16(bitfield1, 0U, 12U) < EverParseGetBitfield16(bitfield0, 0U, 6U);
    uint64_t
    positionAfterBitfield11 =
      EverParseCheckConstraintOk(bitfield1constraintIsOk,
        positionAfterBitfield1);
    if (EverParseIsError(positionAfterBitfield11))
    {
      positionAfterBf2bis0 = positionAfterBitfield11;
    }
    else
    {
      /* Validating field z */
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      BOOLEAN hasBytes = 1ULL <= (InputLength - positionAfterBitfield11);
      uint64_t positionAfterBf2bis1;
      if (hasBytes)
      {
        positionAfterBf2bis1 = positionAfterBitfield11 + 1ULL;
      }
      else
      {
        positionAfterBf2bis1 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterBitfield11);
      }
      uint64_t res;
      if (EverParseIsSuccess(positionAfterBf2bis1))
      {
        res = positionAfterBf2bis1;
      }
      else
      {
        ErrorHandlerFn("_BF2bis",
          "z",
          EverParseErrorReasonOfResult(positionAfterBf2bis1),
          EverParseGetValidatorErrorKind(positionAfterBf2bis1),
          Ctxt,
          Input,
          positionAfterBitfield11);
        res = positionAfterBf2bis1;
      }
      positionAfterBf2bis0 = res;
    }
  }
  if (EverParseIsSuccess(positionAfterBf2bis0))
  {
    return positionAfterBf2bis0;
  }
  ErrorHandlerFn("_BF2bis",
    "__bitfield_1",
    EverParseErrorReasonOfResult(positionAfterBf2bis0),
    EverParseGetValidatorErrorKind(positionAfterBf2bis0),
    Ctxt,
    Input,
    positionAfterBitfield0);
  return positionAfterBf2bis0;
}

static inline uint64_t
ValidateBf3(
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
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength - StartPosition);
  uint64_t positionAfterBf3;
  if (hasBytes0)
  {
    positionAfterBf3 = StartPosition + 2ULL;
  }
  else
  {
    positionAfterBf3 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterBitfield0;
  if (EverParseIsSuccess(positionAfterBf3))
  {
    positionAfterBitfield0 = positionAfterBf3;
  }
  else
  {
    ErrorHandlerFn("_BF3",
      "__bitfield_0",
      EverParseErrorReasonOfResult(positionAfterBf3),
      EverParseGetValidatorErrorKind(positionAfterBf3),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBitfield0 = positionAfterBf3;
  }
  if (EverParseIsError(positionAfterBitfield0))
  {
    return positionAfterBitfield0;
  }
  uint16_t bitfield0 = Load16Be(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength - positionAfterBitfield0);
  uint64_t positionAfterBitfield1;
  if (hasBytes1)
  {
    positionAfterBitfield1 = positionAfterBitfield0 + 2ULL;
  }
  else
  {
    positionAfterBitfield1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBitfield0);
  }
  uint64_t positionAfterBf30;
  if (EverParseIsError(positionAfterBitfield1))
  {
    positionAfterBf30 = positionAfterBitfield1;
  }
  else
  {
    uint16_t bitfield1 = Load16Be(Input + (uint32_t)positionAfterBitfield0);
    BOOLEAN
    bitfield1constraintIsOk =
      EverParseGetBitfield16MsbFirst(bitfield1, 0U, 12U) <
        EverParseGetBitfield16MsbFirst(bitfield0,
          0U,
          6U);
    uint64_t
    positionAfterBitfield11 =
      EverParseCheckConstraintOk(bitfield1constraintIsOk,
        positionAfterBitfield1);
    if (EverParseIsError(positionAfterBitfield11))
    {
      positionAfterBf30 = positionAfterBitfield11;
    }
    else
    {
      /* Validating field z */
      /* Checking that we have enough space for a UINT8BE, i.e., 1 byte */
      BOOLEAN hasBytes = 1ULL <= (InputLength - positionAfterBitfield11);
      uint64_t positionAfterBf31;
      if (hasBytes)
      {
        positionAfterBf31 = positionAfterBitfield11 + 1ULL;
      }
      else
      {
        positionAfterBf31 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterBitfield11);
      }
      uint64_t res;
      if (EverParseIsSuccess(positionAfterBf31))
      {
        res = positionAfterBf31;
      }
      else
      {
        ErrorHandlerFn("_BF3",
          "z",
          EverParseErrorReasonOfResult(positionAfterBf31),
          EverParseGetValidatorErrorKind(positionAfterBf31),
          Ctxt,
          Input,
          positionAfterBitfield11);
        res = positionAfterBf31;
      }
      positionAfterBf30 = res;
    }
  }
  if (EverParseIsSuccess(positionAfterBf30))
  {
    return positionAfterBf30;
  }
  ErrorHandlerFn("_BF3",
    "__bitfield_1",
    EverParseErrorReasonOfResult(positionAfterBf30),
    EverParseGetValidatorErrorKind(positionAfterBf30),
    Ctxt,
    Input,
    positionAfterBitfield0);
  return positionAfterBf30;
}

uint64_t
BfValidateDummy(
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
  /* Validating field emp2 */
  uint64_t
  positionAfterDummy = ValidateBf2bis(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfteremp2;
  if (EverParseIsSuccess(positionAfterDummy))
  {
    positionAfteremp2 = positionAfterDummy;
  }
  else
  {
    ErrorHandlerFn("_dummy",
      "emp2",
      EverParseErrorReasonOfResult(positionAfterDummy),
      EverParseGetValidatorErrorKind(positionAfterDummy),
      Ctxt,
      Input,
      StartPosition);
    positionAfteremp2 = positionAfterDummy;
  }
  if (EverParseIsError(positionAfteremp2))
  {
    return positionAfteremp2;
  }
  /* Validating field emp3 */
  uint64_t
  positionAfterDummy0 = ValidateBf3(Ctxt, ErrorHandlerFn, Input, InputLength, positionAfteremp2);
  if (EverParseIsSuccess(positionAfterDummy0))
  {
    return positionAfterDummy0;
  }
  ErrorHandlerFn("_dummy",
    "emp3",
    EverParseErrorReasonOfResult(positionAfterDummy0),
    EverParseGetValidatorErrorKind(positionAfterDummy0),
    Ctxt,
    Input,
    positionAfteremp2);
  return positionAfterDummy0;
}

