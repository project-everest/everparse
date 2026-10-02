

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
  uint64_t resForPairThird;
  uint64_t positionAfterPairOrError;
  if (hasBytesForPairThird)
  {
    resForPairThird = StartPosition + 12ULL;
  }
  else
  {
    resForPairThird =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfterPairOrError = resForPairThird;
  if (EverParseIsSuccess(positionAfterPairOrError))
  {
    return positionAfterPairOrError;
  }
  ErrorHandlerFn("_Triple",
    "pair",
    EverParseErrorReasonOfResult(positionAfterPairOrError),
    EverParseGetValidatorErrorKind(positionAfterPairOrError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterPairOrError;
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
  uint64_t resFor1234;
  uint64_t positionAfter12orError;
  if (hasBytesFor1234)
  {
    resFor1234 = StartPosition + 16ULL;
  }
  else
  {
    resFor1234 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  positionAfter12orError = resFor1234;
  if (EverParseIsSuccess(positionAfter12orError))
  {
    return positionAfter12orError;
  }
  ErrorHandlerFn("_Quad",
    "_12",
    EverParseErrorReasonOfResult(positionAfter12orError),
    EverParseGetValidatorErrorKind(positionAfter12orError),
    Ctxt,
    Input,
    StartPosition);
  return positionAfter12orError;
}

