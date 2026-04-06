

#include "GetFieldPtr.h"

uint64_t
GetFieldPtrValidateT(
  uint8_t **Out,
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
  /* Validating field f1 */
  BOOLEAN hasBytes0 = (uint64_t)10U <= (InputLength - StartPosition);
  uint64_t res0;
  uint64_t positionAfterT;
  uint64_t positionAfterf1;
  BOOLEAN hasBytes;
  uint64_t res;
  uint64_t positionAfterT0;
  uint64_t positionAfterf2;
  uint64_t positionAfterT1;
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
  positionAfterT = res0;
  if (EverParseIsSuccess(positionAfterT))
  {
    positionAfterf1 = positionAfterT;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f1",
      EverParseErrorReasonOfResult(positionAfterT),
      EverParseGetValidatorErrorKind(positionAfterT),
      Ctxt,
      Input,
      StartPosition);
    positionAfterf1 = positionAfterT;
  }
  if (EverParseIsError(positionAfterf1))
  {
    return positionAfterf1;
  }
  /* Validating field f2 */
  hasBytes = (uint64_t)20U <= (InputLength - positionAfterf1);
  if (hasBytes)
  {
    res = positionAfterf1 + (uint64_t)20U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, positionAfterf1);
  }
  positionAfterT0 = res;
  if (EverParseIsSuccess(positionAfterT0))
  {
    positionAfterf2 = positionAfterT0;
  }
  else
  {
    ErrorHandlerFn("_T",
      "f2.base",
      EverParseErrorReasonOfResult(positionAfterT0),
      EverParseGetValidatorErrorKind(positionAfterT0),
      Ctxt,
      Input,
      positionAfterf1);
    positionAfterf2 = positionAfterT0;
  }
  if (EverParseIsSuccess(positionAfterf2))
  {
    hd = Input + (uint32_t)positionAfterf1;
    *Out = hd;
    actionSuccessF2 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionSuccessF2);
    positionAfterT1 = positionAfterf2;
  }
  else
  {
    positionAfterT1 = positionAfterf2;
  }
  if (EverParseIsSuccess(positionAfterT1))
  {
    return positionAfterT1;
  }
  ErrorHandlerFn("_T",
    "f2",
    EverParseErrorReasonOfResult(positionAfterT1),
    EverParseGetValidatorErrorKind(positionAfterT1),
    Ctxt,
    Input,
    positionAfterf1);
  return positionAfterT1;
}

uint64_t
GetFieldPtrValidateTact(
  uint8_t **Out,
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
  /* Validating field f1 */
  BOOLEAN hasBytes0 = (uint64_t)10U <= (InputLength - StartPosition);
  uint64_t res0;
  uint64_t positionAfterTact;
  uint64_t positionAfterf1;
  BOOLEAN hasBytes;
  uint64_t res;
  uint64_t positionAfterTact0;
  uint64_t positionAfterf2;
  uint64_t positionAfterTact1;
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
  positionAfterTact = res0;
  if (EverParseIsSuccess(positionAfterTact))
  {
    positionAfterf1 = positionAfterTact;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f1",
      EverParseErrorReasonOfResult(positionAfterTact),
      EverParseGetValidatorErrorKind(positionAfterTact),
      Ctxt,
      Input,
      StartPosition);
    positionAfterf1 = positionAfterTact;
  }
  if (EverParseIsError(positionAfterf1))
  {
    return positionAfterf1;
  }
  /* Validating field f2 */
  hasBytes = (uint64_t)20U <= (InputLength - positionAfterf1);
  if (hasBytes)
  {
    res = positionAfterf1 + (uint64_t)20U;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, positionAfterf1);
  }
  positionAfterTact0 = res;
  if (EverParseIsSuccess(positionAfterTact0))
  {
    positionAfterf2 = positionAfterTact0;
  }
  else
  {
    ErrorHandlerFn("_TAct",
      "f2.base",
      EverParseErrorReasonOfResult(positionAfterTact0),
      EverParseGetValidatorErrorKind(positionAfterTact0),
      Ctxt,
      Input,
      positionAfterf1);
    positionAfterf2 = positionAfterTact0;
  }
  if (EverParseIsSuccess(positionAfterf2))
  {
    hd = Input + (uint32_t)positionAfterf1;
    *Out = hd;
    actionSuccessF2 = TRUE;
    KRML_MAYBE_UNUSED_VAR(actionSuccessF2);
    positionAfterTact1 = positionAfterf2;
  }
  else
  {
    positionAfterTact1 = positionAfterf2;
  }
  if (EverParseIsSuccess(positionAfterTact1))
  {
    return positionAfterTact1;
  }
  ErrorHandlerFn("_TAct",
    "f2",
    EverParseErrorReasonOfResult(positionAfterTact1),
    EverParseGetValidatorErrorKind(positionAfterTact1),
    Ctxt,
    Input,
    positionAfterf1);
  return positionAfterTact1;
}

