

#include "Derived.h"

uint64_t
DerivedValidateTriple(
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
  /* SNIPPET_START: Triple */
  uint64_t
  positionAfterTriple = BaseValidatePair(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfterpair;
  if (EverParseIsSuccess(positionAfterTriple))
  {
    positionAfterpair = positionAfterTriple;
  }
  else
  {
    ErrorHandlerFn("_Triple",
      "pair",
      EverParseErrorReasonOfResult(positionAfterTriple),
      EverParseGetValidatorErrorKind(positionAfterTriple),
      Ctxt,
      Input,
      StartPosition);
    positionAfterpair = positionAfterTriple;
  }
  if (EverParseIsError(positionAfterpair))
  {
    return positionAfterpair;
  }
  /* Validating field third */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - positionAfterpair);
  uint64_t positionAfterTriple0;
  if (hasBytes)
  {
    positionAfterTriple0 = positionAfterpair + (uint64_t)4U;
  }
  else
  {
    positionAfterTriple0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterpair);
  }
  if (EverParseIsSuccess(positionAfterTriple0))
  {
    return positionAfterTriple0;
  }
  ErrorHandlerFn("_Triple",
    "third",
    EverParseErrorReasonOfResult(positionAfterTriple0),
    EverParseGetValidatorErrorKind(positionAfterTriple0),
    Ctxt,
    Input,
    positionAfterpair);
  return positionAfterTriple0;
}

uint64_t
DerivedValidateQuad(
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
  /* Validating field _12 */
  uint64_t
  positionAfterQuad = BaseValidatePair(Ctxt, ErrorHandlerFn, Input, InputLength, StartPosition);
  uint64_t positionAfter12;
  if (EverParseIsSuccess(positionAfterQuad))
  {
    positionAfter12 = positionAfterQuad;
  }
  else
  {
    ErrorHandlerFn("_Quad",
      "_12",
      EverParseErrorReasonOfResult(positionAfterQuad),
      EverParseGetValidatorErrorKind(positionAfterQuad),
      Ctxt,
      Input,
      StartPosition);
    positionAfter12 = positionAfterQuad;
  }
  if (EverParseIsError(positionAfter12))
  {
    return positionAfter12;
  }
  /* Validating field _34 */
  uint64_t
  positionAfterQuad0 =
    BaseValidatePair(Ctxt,
      ErrorHandlerFn,
      Input,
      InputLength,
      positionAfter12);
  if (EverParseIsSuccess(positionAfterQuad0))
  {
    return positionAfterQuad0;
  }
  ErrorHandlerFn("_Quad",
    "_34",
    EverParseErrorReasonOfResult(positionAfterQuad0),
    EverParseGetValidatorErrorKind(positionAfterQuad0),
    Ctxt,
    Input,
    positionAfter12);
  return positionAfterQuad0;
}

