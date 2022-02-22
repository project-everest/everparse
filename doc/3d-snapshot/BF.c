

#include "BF.h"


#include "EverParse.h"
uint64_t
BfValidateDummy(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field emp */
  uint64_t positionAfterDummy = StartPosition;
  if (EverParseIsSuccess(positionAfterDummy))
  {
    return positionAfterDummy;
  }
  Err("_dummy",
    "emp",
    EverParseErrorReasonOfResult(positionAfterDummy),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterDummy;
}

