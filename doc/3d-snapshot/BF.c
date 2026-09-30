

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
  BOOLEAN hasBytesForBitfield0 = (InputLength - StartPosition) >= 2ULL;
  uint64_t positionAfterBitfield0orError;
  uint64_t positionAfterBitfield0;
  uint16_t bitfield0;
  BOOLEAN hasBytesForBitfield1;
  uint64_t positionAfterBitfield1;
  uint64_t positionAfterBitfield1orError;
  uint16_t bitfield1;
  BOOLEAN bitfield1constraintIsOk;
  uint64_t positionAfterCheckedBitfield1;
  BOOLEAN hasBytesForZ;
  uint64_t positionAfterZOrError;
  uint64_t resForBitfield1;
  if (hasBytesForBitfield0)
  {
    positionAfterBitfield0orError = StartPosition + 2ULL;
  }
  else
  {
    positionAfterBitfield0orError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBitfield0orError))
  {
    positionAfterBitfield0 = positionAfterBitfield0orError;
  }
  else
  {
    ErrorHandlerFn("_BF2bis",
      "__bitfield_0",
      EverParseErrorReasonOfResult(positionAfterBitfield0orError),
      EverParseGetValidatorErrorKind(positionAfterBitfield0orError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBitfield0 = positionAfterBitfield0orError;
  }
  if (EverParseIsError(positionAfterBitfield0))
  {
    return positionAfterBitfield0;
  }
  bitfield0 = Load16Le(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  hasBytesForBitfield1 = (InputLength - positionAfterBitfield0) >= 2ULL;
  if (hasBytesForBitfield1)
  {
    positionAfterBitfield1 = positionAfterBitfield0 + 2ULL;
  }
  else
  {
    positionAfterBitfield1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBitfield0);
  }
  if (EverParseIsError(positionAfterBitfield1))
  {
    positionAfterBitfield1orError = positionAfterBitfield1;
  }
  else
  {
    bitfield1 = Load16Le(Input + (uint32_t)positionAfterBitfield0);
    bitfield1constraintIsOk =
      EverParseGetBitfield16(bitfield1, 0U, 12U) < EverParseGetBitfield16(bitfield0, 0U, 6U);
    positionAfterCheckedBitfield1 =
      EverParseCheckConstraintOk(bitfield1constraintIsOk,
        positionAfterBitfield1);
    if (EverParseIsError(positionAfterCheckedBitfield1))
    {
      positionAfterBitfield1orError = positionAfterCheckedBitfield1;
    }
    else
    {
      /* Validating field z */
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      hasBytesForZ = (InputLength - positionAfterCheckedBitfield1) >= 1ULL;
      if (hasBytesForZ)
      {
        positionAfterZOrError = positionAfterCheckedBitfield1 + 1ULL;
      }
      else
      {
        positionAfterZOrError =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedBitfield1);
      }
      if (EverParseIsSuccess(positionAfterZOrError))
      {
        resForBitfield1 = positionAfterZOrError;
      }
      else
      {
        ErrorHandlerFn("_BF2bis",
          "z",
          EverParseErrorReasonOfResult(positionAfterZOrError),
          EverParseGetValidatorErrorKind(positionAfterZOrError),
          Ctxt,
          Input,
          positionAfterCheckedBitfield1);
        resForBitfield1 = positionAfterZOrError;
      }
      positionAfterBitfield1orError = resForBitfield1;
    }
  }
  if (EverParseIsSuccess(positionAfterBitfield1orError))
  {
    return positionAfterBitfield1orError;
  }
  ErrorHandlerFn("_BF2bis",
    "__bitfield_1",
    EverParseErrorReasonOfResult(positionAfterBitfield1orError),
    EverParseGetValidatorErrorKind(positionAfterBitfield1orError),
    Ctxt,
    Input,
    positionAfterBitfield0);
  return positionAfterBitfield1orError;
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
  BOOLEAN hasBytesForBitfield0 = (InputLength - StartPosition) >= 2ULL;
  uint64_t positionAfterBitfield0orError;
  uint64_t positionAfterBitfield0;
  uint16_t bitfield0;
  BOOLEAN hasBytesForBitfield1;
  uint64_t positionAfterBitfield1;
  uint64_t positionAfterBitfield1orError;
  uint16_t bitfield1;
  BOOLEAN bitfield1constraintIsOk;
  uint64_t positionAfterCheckedBitfield1;
  BOOLEAN hasBytesForZ;
  uint64_t positionAfterZOrError;
  uint64_t resForBitfield1;
  if (hasBytesForBitfield0)
  {
    positionAfterBitfield0orError = StartPosition + 2ULL;
  }
  else
  {
    positionAfterBitfield0orError =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  if (EverParseIsSuccess(positionAfterBitfield0orError))
  {
    positionAfterBitfield0 = positionAfterBitfield0orError;
  }
  else
  {
    ErrorHandlerFn("_BF3",
      "__bitfield_0",
      EverParseErrorReasonOfResult(positionAfterBitfield0orError),
      EverParseGetValidatorErrorKind(positionAfterBitfield0orError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterBitfield0 = positionAfterBitfield0orError;
  }
  if (EverParseIsError(positionAfterBitfield0))
  {
    return positionAfterBitfield0;
  }
  bitfield0 = Load16Be(Input + (uint32_t)StartPosition);
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  hasBytesForBitfield1 = (InputLength - positionAfterBitfield0) >= 2ULL;
  if (hasBytesForBitfield1)
  {
    positionAfterBitfield1 = positionAfterBitfield0 + 2ULL;
  }
  else
  {
    positionAfterBitfield1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBitfield0);
  }
  if (EverParseIsError(positionAfterBitfield1))
  {
    positionAfterBitfield1orError = positionAfterBitfield1;
  }
  else
  {
    bitfield1 = Load16Be(Input + (uint32_t)positionAfterBitfield0);
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
      positionAfterBitfield1orError = positionAfterCheckedBitfield1;
    }
    else
    {
      /* Validating field z */
      /* Checking that we have enough space for a UINT8BE, i.e., 1 byte */
      hasBytesForZ = (InputLength - positionAfterCheckedBitfield1) >= 1ULL;
      if (hasBytesForZ)
      {
        positionAfterZOrError = positionAfterCheckedBitfield1 + 1ULL;
      }
      else
      {
        positionAfterZOrError =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterCheckedBitfield1);
      }
      if (EverParseIsSuccess(positionAfterZOrError))
      {
        resForBitfield1 = positionAfterZOrError;
      }
      else
      {
        ErrorHandlerFn("_BF3",
          "z",
          EverParseErrorReasonOfResult(positionAfterZOrError),
          EverParseGetValidatorErrorKind(positionAfterZOrError),
          Ctxt,
          Input,
          positionAfterCheckedBitfield1);
        resForBitfield1 = positionAfterZOrError;
      }
      positionAfterBitfield1orError = resForBitfield1;
    }
  }
  if (EverParseIsSuccess(positionAfterBitfield1orError))
  {
    return positionAfterBitfield1orError;
  }
  ErrorHandlerFn("_BF3",
    "__bitfield_1",
    EverParseErrorReasonOfResult(positionAfterBitfield1orError),
    EverParseGetValidatorErrorKind(positionAfterBitfield1orError),
    Ctxt,
    Input,
    positionAfterBitfield0);
  return positionAfterBitfield1orError;
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
  positionAfterEmp2OrError =
    ValidateBf2bis(Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      StartPosition);
  uint64_t positionAfterEmp2;
  uint64_t positionAfterEmp3OrError;
  if (EverParseIsSuccess(positionAfterEmp2OrError))
  {
    positionAfterEmp2 = positionAfterEmp2OrError;
  }
  else
  {
    ErrorHandlerFn("_dummy",
      "emp2",
      EverParseErrorReasonOfResult(positionAfterEmp2OrError),
      EverParseGetValidatorErrorKind(positionAfterEmp2OrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterEmp2 = positionAfterEmp2OrError;
  }
  if (EverParseIsError(positionAfterEmp2))
  {
    return positionAfterEmp2;
  }
  /* Validating field emp3 */
  positionAfterEmp3OrError =
    ValidateBf3(Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAfterEmp2);
  if (EverParseIsSuccess(positionAfterEmp3OrError))
  {
    return positionAfterEmp3OrError;
  }
  ErrorHandlerFn("_dummy",
    "emp3",
    EverParseErrorReasonOfResult(positionAfterEmp3OrError),
    EverParseGetValidatorErrorKind(positionAfterEmp3OrError),
    Ctxt,
    Input,
    positionAfterEmp2);
  return positionAfterEmp3OrError;
}

