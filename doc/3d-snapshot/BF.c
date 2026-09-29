

#include "BF.h"

#include "EverParse.h"

static inline uint64_t
ValidateBf2bis(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 2ULL;
  uint64_t positionAfterBitfield0;
  uint64_t positionAfterBitfield00;
  uint16_t bitfield0;
  BOOLEAN hasBytes1;
  uint64_t positionAfterBitfield1;
  uint64_t positionAfterBitfield10;
  uint16_t bitfield1;
  BOOLEAN bitfield1constraintIsOk;
  uint64_t positionAfterCheckedBitfield1;
  BOOLEAN hasBytes;
  uint64_t positionAfterZ;
  uint64_t res;
  if (hasBytes0)
  {
    positionAfterBitfield0 = StartPosition + 2ULL;
  }
  else
  {
    positionAfterBitfield0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBitfield0))
  {
    positionAfterBitfield00 = positionAfterBitfield0;
  }
  else
  {
    ErrorHandlerFn("_BF2bis",
      "__bitfield_0",
      EverParseErrorReasonOfResult(positionAfterBitfield0),
      EverParseGetValidatorErrorKind(positionAfterBitfield0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBitfield00 = positionAfterBitfield0;
  }
  if (EverParseIsError(positionAfterBitfield00))
  {
    return positionAfterBitfield00;
  }
  bitfield0 = Load16Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  hasBytes1 = (InputLength - positionAfterBitfield00) >= 2ULL;
  if (hasBytes1)
  {
    positionAfterBitfield1 = positionAfterBitfield00 + 2ULL;
  }
  else
  {
    positionAfterBitfield1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBitfield00);
  }
  if (EverParseIsError(positionAfterBitfield1))
  {
    positionAfterBitfield10 = positionAfterBitfield1;
  }
  else
  {
    bitfield1 = Load16Le(Input + (uint32_t)positionAfterBitfield00);
    bitfield1constraintIsOk =
      EverParseGetBitfield16(bitfield1, 0U, 12U) < EverParseGetBitfield16(bitfield0, 0U, 6U);
    positionAfterCheckedBitfield1 =
      EverParseCheckConstraintOk(bitfield1constraintIsOk,
        positionAfterBitfield1);
    if (EverParseIsError(positionAfterCheckedBitfield1))
    {
      positionAfterBitfield10 = positionAfterCheckedBitfield1;
    }
    else
    {
      /* Validating field z */
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      hasBytes = (InputLength - positionAfterCheckedBitfield1) >= 1ULL;
      if (hasBytes)
      {
        positionAfterZ = positionAfterCheckedBitfield1 + 1ULL;
      }
      else
      {
        positionAfterZ =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedBitfield1);
      }
      if (EverParseIsSuccess(positionAfterZ))
      {
        res = positionAfterZ;
      }
      else
      {
        ErrorHandlerFn("_BF2bis",
          "z",
          EverParseErrorReasonOfResult(positionAfterZ),
          EverParseGetValidatorErrorKind(positionAfterZ),
          Ctxt,
          Input,
          positionAfterCheckedBitfield1);
        res = positionAfterZ;
      }
      positionAfterBitfield10 = res;
    }
  }
  if (EverParseIsSuccess(positionAfterBitfield10))
  {
    return positionAfterBitfield10;
  }
  ErrorHandlerFn("_BF2bis",
    "__bitfield_1",
    EverParseErrorReasonOfResult(positionAfterBitfield10),
    EverParseGetValidatorErrorKind(positionAfterBitfield10),
    Ctxt,
    Input,
    positionAfterBitfield00);
  return positionAfterBitfield10;
}

static inline uint64_t
ValidateBf3(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 2ULL;
  uint64_t positionAfterBitfield0;
  uint64_t positionAfterBitfield00;
  uint16_t bitfield0;
  BOOLEAN hasBytes1;
  uint64_t positionAfterBitfield1;
  uint64_t positionAfterBitfield10;
  uint16_t bitfield1;
  BOOLEAN bitfield1constraintIsOk;
  uint64_t positionAfterCheckedBitfield1;
  BOOLEAN hasBytes;
  uint64_t positionAfterZ;
  uint64_t res;
  if (hasBytes0)
  {
    positionAfterBitfield0 = StartPosition + 2ULL;
  }
  else
  {
    positionAfterBitfield0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBitfield0))
  {
    positionAfterBitfield00 = positionAfterBitfield0;
  }
  else
  {
    ErrorHandlerFn("_BF3",
      "__bitfield_0",
      EverParseErrorReasonOfResult(positionAfterBitfield0),
      EverParseGetValidatorErrorKind(positionAfterBitfield0),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBitfield00 = positionAfterBitfield0;
  }
  if (EverParseIsError(positionAfterBitfield00))
  {
    return positionAfterBitfield00;
  }
  bitfield0 = Load16Be(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  hasBytes1 = (InputLength - positionAfterBitfield00) >= 2ULL;
  if (hasBytes1)
  {
    positionAfterBitfield1 = positionAfterBitfield00 + 2ULL;
  }
  else
  {
    positionAfterBitfield1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBitfield00);
  }
  if (EverParseIsError(positionAfterBitfield1))
  {
    positionAfterBitfield10 = positionAfterBitfield1;
  }
  else
  {
    bitfield1 = Load16Be(Input + (uint32_t)positionAfterBitfield00);
    bitfield1constraintIsOk =
      EverParseGetBitfield16MsbFirst(bitfield1, 0U, 12U) <
        EverParseGetBitfield16MsbFirst(bitfield0,
          0U,
          6U);
    positionAfterCheckedBitfield1 =
      EverParseCheckConstraintOk(bitfield1constraintIsOk,
        positionAfterBitfield1);
    if (EverParseIsError(positionAfterCheckedBitfield1))
    {
      positionAfterBitfield10 = positionAfterCheckedBitfield1;
    }
    else
    {
      /* Validating field z */
      /* Checking that we have enough space for a UINT8BE, i.e., 1 byte */
      hasBytes = (InputLength - positionAfterCheckedBitfield1) >= 1ULL;
      if (hasBytes)
      {
        positionAfterZ = positionAfterCheckedBitfield1 + 1ULL;
      }
      else
      {
        positionAfterZ =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedBitfield1);
      }
      if (EverParseIsSuccess(positionAfterZ))
      {
        res = positionAfterZ;
      }
      else
      {
        ErrorHandlerFn("_BF3",
          "z",
          EverParseErrorReasonOfResult(positionAfterZ),
          EverParseGetValidatorErrorKind(positionAfterZ),
          Ctxt,
          Input,
          positionAfterCheckedBitfield1);
        res = positionAfterZ;
      }
      positionAfterBitfield10 = res;
    }
  }
  if (EverParseIsSuccess(positionAfterBitfield10))
  {
    return positionAfterBitfield10;
  }
  ErrorHandlerFn("_BF3",
    "__bitfield_1",
    EverParseErrorReasonOfResult(positionAfterBitfield10),
    EverParseGetValidatorErrorKind(positionAfterBitfield10),
    Ctxt,
    Input,
    positionAfterBitfield00);
  return positionAfterBitfield10;
}

uint64_t
BfValidateDummy(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field emp2 */
  uint64_t
  positionAfterEmp20 = ValidateBf2bis(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfterEmp2;
  uint64_t positionAfterEmp3;
  if (EverParseIsSuccess(positionAfterEmp20))
  {
    positionAfterEmp2 = positionAfterEmp20;
  }
  else
  {
    ErrorHandlerFn("_dummy",
      "emp2",
      EverParseErrorReasonOfResult(positionAfterEmp20),
      EverParseGetValidatorErrorKind(positionAfterEmp20),
      Ctxt,
      Input,
      StartPosition);
    positionAfterEmp2 = positionAfterEmp20;
  }
  if (EverParseIsError(positionAfterEmp2))
  {
    return positionAfterEmp2;
  }
  /* Validating field emp3 */
  positionAfterEmp3 = ValidateBf3(Ctxt, ErrorHandlerFn, Input, InputLength, positionAfterEmp2);
  if (EverParseIsSuccess(positionAfterEmp3))
  {
    return positionAfterEmp3;
  }
  ErrorHandlerFn("_dummy",
    "emp3",
    EverParseErrorReasonOfResult(positionAfterEmp3),
    EverParseGetValidatorErrorKind(positionAfterEmp3),
    Ctxt,
    Input,
    positionAfterEmp2);
  return positionAfterEmp3;
}

