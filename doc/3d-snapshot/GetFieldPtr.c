

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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= (uint64_t)10U;
  uint64_t res0;
  uint64_t positionAfterf10;
  uint64_t positionAfterf1;
  BOOLEAN hasBytes;
  uint64_t res;
  uint64_t positionAfterf2_base;
  uint64_t positionAfterf20;
  uint64_t positionAfterf2;
  uint8_t *hd;
  BOOLEAN actionSuccessF2;
  if (hasBytes0)
  {
    res0 = StartPosition + (uint64_t)10U;
  }
  else
  {
    res0 = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterf10 = res0;
  if (EverParseIsSuccess(positionAfterf10))
  {
    positionAfterf1 = positionAfterf10;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f1",
      EverParseErrorReasonOfResult(positionAfterf10),
      EverParseGetValidatorErrorKind(positionAfterf10),
      Ctxt,
      Input,
      StartPosition);
    positionAfterf1 = positionAfterf10;
  }
  if (EverParseIsError(positionAfterf1))
  {
    return positionAfterf1;
  }
  /* Validating field f2 */
  hasBytes = (InputLength - positionAfterf1) >= (uint64_t)20U;
  if (hasBytes)
  {
    res = positionAfterf1 + (uint64_t)20U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, positionAfterf1);
  }
  positionAfterf2_base = res;
  if (EverParseIsSuccess(positionAfterf2_base))
  {
    positionAfterf20 = positionAfterf2_base;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f2.base",
      EverParseErrorReasonOfResult(positionAfterf2_base),
      EverParseGetValidatorErrorKind(positionAfterf2_base),
      Ctxt,
      Input,
      positionAfterf1);
    positionAfterf20 = positionAfterf2_base;
  }
  if (EverParseIsSuccess(positionAfterf20))
  {
    hd = Input + (uint32_t)positionAfterf1;
    *Out = hd;
    actionSuccessF2 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionSuccessF2);
    positionAfterf2 = positionAfterf20;
  }
  else
  {
    positionAfterf2 = positionAfterf20;
  }
  if (EverParseIsSuccess(positionAfterf2))
  {
    return positionAfterf2;
  }
  ErrorHandlerFn("_T",
    "f2",
    EverParseErrorReasonOfResult(positionAfterf2),
    EverParseGetValidatorErrorKind(positionAfterf2),
    Ctxt,
    Input,
    positionAfterf1);
  return positionAfterf2;
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
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= (uint64_t)10U;
  uint64_t res0;
  uint64_t positionAfterf10;
  uint64_t positionAfterf1;
  BOOLEAN hasBytes;
  uint64_t res;
  uint64_t positionAfterf2_base;
  uint64_t positionAfterf20;
  uint64_t positionAfterf2;
  uint8_t *hd;
  BOOLEAN actionSuccessF2;
  if (hasBytes0)
  {
    res0 = StartPosition + (uint64_t)10U;
  }
  else
  {
    res0 = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterf10 = res0;
  if (EverParseIsSuccess(positionAfterf10))
  {
    positionAfterf1 = positionAfterf10;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f1",
      EverParseErrorReasonOfResult(positionAfterf10),
      EverParseGetValidatorErrorKind(positionAfterf10),
      Ctxt,
      Input,
      StartPosition);
    positionAfterf1 = positionAfterf10;
  }
  if (EverParseIsError(positionAfterf1))
  {
    return positionAfterf1;
  }
  /* Validating field f2 */
  hasBytes = (InputLength - positionAfterf1) >= (uint64_t)20U;
  if (hasBytes)
  {
    res = positionAfterf1 + (uint64_t)20U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, positionAfterf1);
  }
  positionAfterf2_base = res;
  if (EverParseIsSuccess(positionAfterf2_base))
  {
    positionAfterf20 = positionAfterf2_base;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f2.base",
      EverParseErrorReasonOfResult(positionAfterf2_base),
      EverParseGetValidatorErrorKind(positionAfterf2_base),
      Ctxt,
      Input,
      positionAfterf1);
    positionAfterf20 = positionAfterf2_base;
  }
  if (EverParseIsSuccess(positionAfterf20))
  {
    hd = Input + (uint32_t)positionAfterf1;
    *Out = hd;
    actionSuccessF2 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionSuccessF2);
    positionAfterf2 = positionAfterf20;
  }
  else
  {
    positionAfterf2 = positionAfterf20;
  }
  if (EverParseIsSuccess(positionAfterf2))
  {
    return positionAfterf2;
  }
  ErrorHandlerFn("_TAct",
    "f2",
    EverParseErrorReasonOfResult(positionAfterf2),
    EverParseGetValidatorErrorKind(positionAfterf2),
    Ctxt,
    Input,
    positionAfterf1);
  return positionAfterf2;
}

