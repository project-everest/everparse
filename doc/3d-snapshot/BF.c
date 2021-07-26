

#include "BF.h"

static inline uint64_t ValidateDummyEmp(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _dummy_emp
        of type BF._dummy
--*/
{
  /* Validating field emp */
  return (uint64_t)0U;
}

uint64_t BfValidateDummy(EverParseInputBuffer Input)
{
  /* Field _dummy_emp */
  return ValidateDummyEmp(Input);
}

void BfReadDummy(EverParseInputBuffer Input)
{
  
}

