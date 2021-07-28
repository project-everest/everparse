

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
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _dummy_emp
        of type BF._dummy
--*/
{
  /* Validating field emp */
  uint32_t positionBeforeDummy = *Input.pos;
  uint64_t resultAfterDummy = (uint64_t)0U;
  if (EverParseIsSuccess(resultAfterDummy))
  {
    return resultAfterDummy;
  }
  Err("_dummy",
    "_dummy_emp",
    EverParseErrorReasonOfResult(resultAfterDummy),
    Ctxt,
    Input,
    positionBeforeDummy);
  return resultAfterDummy;
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
  EverParseInputBuffer Input
)
{
  /* Field _dummy_emp */
  uint32_t positionBeforeDummy = *Input.pos;
  uint64_t resultAfterDummy = ValidateDummyEmp(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterDummy))
  {
    return resultAfterDummy;
  }
  Err("_dummy",
    "emp",
    EverParseErrorReasonOfResult(resultAfterDummy),
    Ctxt,
    Input,
    positionBeforeDummy);
  return resultAfterDummy;
}

void BfReadDummy(EverParseInputBuffer Input)
{
  
}

