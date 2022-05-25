

#include "BF.h"



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
  /* Validating field emp1 */
  uint64_t positionAfterDummy = StartPosition;
  uint64_t positionAfteremp1;
  if (EverParseIsSuccess(positionAfterDummy))
  {
    positionAfteremp1 = positionAfterDummy;
  }
  else
  {
    Err("_dummy",
      "emp1",
      EverParseErrorReasonOfResult(positionAfterDummy),
      Ctxt,
      Input,
      StartPosition);
    positionAfteremp1 = positionAfterDummy;
  }
  if (EverParseIsError(positionAfteremp1))
  {
    return positionAfteremp1;
  }
  /* Validating field emp2 */
  uint64_t positionAfterDummy0 = positionAfteremp1;
  if (EverParseIsSuccess(positionAfterDummy0))
  {
    return positionAfterDummy0;
  }
  Err("_dummy",
    "emp2",
    EverParseErrorReasonOfResult(positionAfterDummy0),
    Ctxt,
    Input,
    positionAfteremp1);
  return positionAfterDummy0;
}

