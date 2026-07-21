

#include "Derived.h"

#include "EverParse.h"

uint64_t
DerivedValidateTriple(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 12ULL;
  uint64_t res;
  uint64_t positionAfterTriple;
  if (hasBytes)
  {
    res = StartPosition + 12ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterTriple = res;
  if (EverParseIsSuccess(positionAfterTriple))
  {
    return positionAfterTriple;
  }
  ErrorHandlerFn("_Triple",
    "pair",
    EverParseErrorReasonOfResult(positionAfterTriple),
    EverParseGetValidatorErrorKind(positionAfterTriple),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterTriple;
}

uint64_t
DerivedValidateQuad(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  BOOLEAN hasBytes = (InputLength - StartPosition) >= 16ULL;
  uint64_t res;
  uint64_t positionAfterQuad;
  if (hasBytes)
  {
    res = StartPosition + 16ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterQuad = res;
  if (EverParseIsSuccess(positionAfterQuad))
  {
    return positionAfterQuad;
  }
  ErrorHandlerFn("_Quad",
    "_12",
    EverParseErrorReasonOfResult(positionAfterQuad),
    EverParseGetValidatorErrorKind(positionAfterQuad),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterQuad;
}

