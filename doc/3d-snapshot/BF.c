

#include "BF.h"

static inline uint64_t
ValidateDummyEmp(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
/*++
    Internal helper function:
        Validator for field _dummy_emp
        of type BF._dummy
--*/
{
  /* Validating field emp */
  uint64_t positionAfterDummy = (uint64_t)Pos;
  if (EverParseIsSuccess(positionAfterDummy))
  {
    return positionAfterDummy;
  }
  Err("_dummy",
    "_dummy_emp",
    EverParseErrorReasonOfResult(positionAfterDummy),
    Ctxt,
    Input,
    Pos);
  return positionAfterDummy;
}

uint64_t
BfValidateDummy(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint32_t x5
  ),
  EverParseInputBuffer Input,
  uint32_t Pos
)
{
  /* Field _dummy_emp */
  uint64_t positionAfterDummy = ValidateDummyEmp(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterDummy))
  {
    return positionAfterDummy;
  }
  Err("_dummy", "emp", EverParseErrorReasonOfResult(positionAfterDummy), Ctxt, Input, Pos);
  return positionAfterDummy;
}

void BfReadDummy(EverParseInputBuffer Input, uint32_t Pos)
{
  
}

