

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
  uint64_t positionAfterF10;
  uint64_t positionAfterF1;
  BOOLEAN hasBytesForF2_base;
  uint64_t resForF2_base;
  uint64_t positionAfterF2_base;
  uint64_t positionAfterF20;
  uint64_t positionAfterF2;
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
  positionAfterF10 = resForF1;
  if (EverParseIsSuccess(positionAfterF10))
  {
    positionAfterF1 = positionAfterF10;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f1",
      EverParseErrorReasonOfResult(positionAfterF10),
      EverParseGetValidatorErrorKind(positionAfterF10),
      Ctxt,
      Input,
      StartPosition);
    positionAfterF1 = positionAfterF10;
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
  positionAfterF2_base = resForF2_base;
  if (EverParseIsSuccess(positionAfterF2_base))
  {
    positionAfterF20 = positionAfterF2_base;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f2.base",
      EverParseErrorReasonOfResult(positionAfterF2_base),
      EverParseGetValidatorErrorKind(positionAfterF2_base),
      Ctxt,
      Input,
      positionAfterF1);
    positionAfterF20 = positionAfterF2_base;
  }
  if (EverParseIsSuccess(positionAfterF20))
  {
    hd = Input + (uint32_t)positionAfterF1;
    *Out = hd;
    actionSuccessF2 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionSuccessF2);
    positionAfterF2 = positionAfterF20;
  }
  else
  {
    positionAfterF2 = positionAfterF20;
  }
  if (EverParseIsSuccess(positionAfterF2))
  {
    return positionAfterF2;
  }
  ErrorHandlerFn("_T",
    "f2",
    EverParseErrorReasonOfResult(positionAfterF2),
    EverParseGetValidatorErrorKind(positionAfterF2),
    Ctxt,
    Input,
    positionAfterF1);
  return positionAfterF2;
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
  uint64_t positionAfterF10;
  uint64_t positionAfterF1;
  BOOLEAN hasBytesForF2_base;
  uint64_t resForF2_base;
  uint64_t positionAfterF2_base;
  uint64_t positionAfterF20;
  uint64_t positionAfterF2;
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
  positionAfterF10 = resForF1;
  if (EverParseIsSuccess(positionAfterF10))
  {
    positionAfterF1 = positionAfterF10;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f1",
      EverParseErrorReasonOfResult(positionAfterF10),
      EverParseGetValidatorErrorKind(positionAfterF10),
      Ctxt,
      Input,
      StartPosition);
    positionAfterF1 = positionAfterF10;
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
  positionAfterF2_base = resForF2_base;
  if (EverParseIsSuccess(positionAfterF2_base))
  {
    positionAfterF20 = positionAfterF2_base;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f2.base",
      EverParseErrorReasonOfResult(positionAfterF2_base),
      EverParseGetValidatorErrorKind(positionAfterF2_base),
      Ctxt,
      Input,
      positionAfterF1);
    positionAfterF20 = positionAfterF2_base;
  }
  if (EverParseIsSuccess(positionAfterF20))
  {
    hd = Input + (uint32_t)positionAfterF1;
    *Out = hd;
    actionSuccessF2 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionSuccessF2);
    positionAfterF2 = positionAfterF20;
  }
  else
  {
    positionAfterF2 = positionAfterF20;
  }
  if (EverParseIsSuccess(positionAfterF2))
  {
    return positionAfterF2;
  }
  ErrorHandlerFn("_TAct",
    "f2",
    EverParseErrorReasonOfResult(positionAfterF2),
    EverParseGetValidatorErrorKind(positionAfterF2),
    Ctxt,
    Input,
    positionAfterF1);
  return positionAfterF2;
}

