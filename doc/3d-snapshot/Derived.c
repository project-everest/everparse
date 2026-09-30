

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
  BOOLEAN hasBytesForPairThird = (InputLength - StartPosition) >= 12ULL;
  uint64_t res;
  uint64_t positionAfterPair;
  if (hasBytesForPairThird)
  {
    res = StartPosition + 12ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfterPair = res;
  if (EverParseIsSuccess(positionAfterPair))
  {
    return positionAfterPair;
  }
  ErrorHandlerFn("_Triple",
    "pair",
    EverParseErrorReasonOfResult(positionAfterPair),
    EverParseGetValidatorErrorKind(positionAfterPair),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPair;
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
  BOOLEAN hasBytesFor1234 = (InputLength - StartPosition) >= 16ULL;
  uint64_t res;
  uint64_t positionAfter12;
  if (hasBytesFor1234)
  {
    res = StartPosition + 16ULL;
  }
  else
  {
    res = EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA, StartPosition);
  }
  positionAfter12 = res;
  if (EverParseIsSuccess(positionAfter12))
  {
    return positionAfter12;
  }
  ErrorHandlerFn("_Quad",
    "_12",
    EverParseErrorReasonOfResult(positionAfter12),
    EverParseGetValidatorErrorKind(positionAfter12),
    Ctxt,
    Input,
    StartPosition);
  return positionAfter12;
}

