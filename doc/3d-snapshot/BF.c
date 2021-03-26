

#include "BF.h"

static inline uint64_t ValidateDummyEmp(uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _dummy_emp
        of type BF._dummy
--*/
{
  /* Validating field emp */
  return StartPosition;
}

uint64_t BfValidateDummy(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _dummy_emp */
  return ValidateDummyEmp(StartPosition);
}

void BfReadDummy(uint32_t InputLength, uint8_t *Input, uint32_t StartPosition)
{
  
}

