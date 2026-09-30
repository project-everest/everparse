

#include "GetFieldPtr.h"

#include "EverParse.h"

uint64_t
GetFieldPtrValidateT(
  uint8_t **Out,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field f1 */
  BOOLEAN hasBytesForF1 = (InputLength - StartPosition) >= (uint64_t)10U;
  uint64_t resForF1;
  uint64_t positionAfterF1OrError;
  uint64_t positionAfterF1;
  BOOLEAN hasBytesForF2_base;
  uint64_t resForF2_base;
  uint64_t positionAfterF2_baseOrError;
  uint64_t positionAfterF2;
  uint64_t positionAfterF2OrError;
  uint8_t *hd;
  BOOLEAN actionSuccessF2;
  if (hasBytesForF1)
  {
    resForF1 = StartPosition + (uint64_t)10U;
  }
  else
  {
    resForF1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterF1OrError = resForF1;
  if (EverParseIsSuccess(positionAfterF1OrError))
  {
    positionAfterF1 = positionAfterF1OrError;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f1",
      EverParseErrorReasonOfResult(positionAfterF1OrError),
      EverParseGetValidatorErrorKind(positionAfterF1OrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterF1 = positionAfterF1OrError;
  }
  if (EverParseIsError(positionAfterF1))
  {
    return positionAfterF1;
  }
  /* Validating field f2 */
  hasBytesForF2_base = (InputLength - positionAfterF1) >= (uint64_t)20U;
  if (hasBytesForF2_base)
  {
    resForF2_base = positionAfterF1 + (uint64_t)20U;
  }
  else
  {
    resForF2_base =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterF1);
  }
  positionAfterF2_baseOrError = resForF2_base;
  if (EverParseIsSuccess(positionAfterF2_baseOrError))
  {
    positionAfterF2 = positionAfterF2_baseOrError;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f2.base",
      EverParseErrorReasonOfResult(positionAfterF2_baseOrError),
      EverParseGetValidatorErrorKind(positionAfterF2_baseOrError),
      Ctxt,
      Input,
      positionAfterF1);
    positionAfterF2 = positionAfterF2_baseOrError;
  }
  if (EverParseIsSuccess(positionAfterF2))
  {
    hd = Input + (uint32_t)positionAfterF1;
    *Out = hd;
    actionSuccessF2 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionSuccessF2);
    positionAfterF2OrError = positionAfterF2;
  }
  else
  {
    positionAfterF2OrError = positionAfterF2;
  }
  if (EverParseIsSuccess(positionAfterF2OrError))
  {
    return positionAfterF2OrError;
  }
  ErrorHandlerFn("_T",
    "f2",
    EverParseErrorReasonOfResult(positionAfterF2OrError),
    EverParseGetValidatorErrorKind(positionAfterF2OrError),
    Ctxt,
    Input,
    positionAfterF1);
  return positionAfterF2OrError;
}

uint64_t
GetFieldPtrValidateTact(
  uint8_t **Out,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field f1 */
  BOOLEAN hasBytesForF1 = (InputLength - StartPosition) >= (uint64_t)10U;
  uint64_t resForF1;
  uint64_t positionAfterF1OrError;
  uint64_t positionAfterF1;
  BOOLEAN hasBytesForF2_base;
  uint64_t resForF2_base;
  uint64_t positionAfterF2_baseOrError;
  uint64_t positionAfterF2;
  uint64_t positionAfterF2OrError;
  uint8_t *hd;
  BOOLEAN actionSuccessF2;
  if (hasBytesForF1)
  {
    resForF1 = StartPosition + (uint64_t)10U;
  }
  else
  {
    resForF1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterF1OrError = resForF1;
  if (EverParseIsSuccess(positionAfterF1OrError))
  {
    positionAfterF1 = positionAfterF1OrError;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f1",
      EverParseErrorReasonOfResult(positionAfterF1OrError),
      EverParseGetValidatorErrorKind(positionAfterF1OrError),
      Ctxt,
      Input,
      StartPosition);
    positionAfterF1 = positionAfterF1OrError;
  }
  if (EverParseIsError(positionAfterF1))
  {
    return positionAfterF1;
  }
  /* Validating field f2 */
  hasBytesForF2_base = (InputLength - positionAfterF1) >= (uint64_t)20U;
  if (hasBytesForF2_base)
  {
    resForF2_base = positionAfterF1 + (uint64_t)20U;
  }
  else
  {
    resForF2_base =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterF1);
  }
  positionAfterF2_baseOrError = resForF2_base;
  if (EverParseIsSuccess(positionAfterF2_baseOrError))
  {
    positionAfterF2 = positionAfterF2_baseOrError;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f2.base",
      EverParseErrorReasonOfResult(positionAfterF2_baseOrError),
      EverParseGetValidatorErrorKind(positionAfterF2_baseOrError),
      Ctxt,
      Input,
      positionAfterF1);
    positionAfterF2 = positionAfterF2_baseOrError;
  }
  if (EverParseIsSuccess(positionAfterF2))
  {
    hd = Input + (uint32_t)positionAfterF1;
    *Out = hd;
    actionSuccessF2 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionSuccessF2);
    positionAfterF2OrError = positionAfterF2;
  }
  else
  {
    positionAfterF2OrError = positionAfterF2;
  }
  if (EverParseIsSuccess(positionAfterF2OrError))
  {
    return positionAfterF2OrError;
  }
  ErrorHandlerFn("_TAct",
    "f2",
    EverParseErrorReasonOfResult(positionAfterF2OrError),
    EverParseGetValidatorErrorKind(positionAfterF2OrError),
    Ctxt,
    Input,
    positionAfterF1);
  return positionAfterF2OrError;
}

