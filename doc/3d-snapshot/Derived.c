

#include "Derived.h"

/*
Auto-generated field identifier for error reporting
*/
#define DERIVED__TRIPLE__THIRD ((uint64_t)26U)

static inline uint64_t ValidateTriplePair(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _Triple_pair
        of type Derived._Triple
--*/
{
  /* SNIPPET_START: Triple */
  return BaseValidatePair(Input);
}

static inline uint64_t ValidateTripleThird(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _Triple_third
        of type Derived._Triple
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field third */
  uint64_t result = BaseValidateUlong(Input);
  return EverParseMaybeSetErrorCode(result, startPosition1, DERIVED__TRIPLE__THIRD);
}

uint64_t DerivedValidateTriple(EverParseInputBuffer Input)
{
  /* Field _Triple_pair */
  uint64_t resultAfterpair = ValidateTriplePair(Input);
  if (EverParseIsError(resultAfterpair))
  {
    return resultAfterpair;
  }
  /* Field _Triple_third */
  uint64_t res = ValidateTripleThird(Input);
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
}

static inline uint64_t ValidateQuad12(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _Quad__12
        of type Derived._Quad
--*/
{
  /* Validating field _12 */
  return BaseValidatePair(Input);
}

static inline uint64_t ValidateQuad34(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _Quad__34
        of type Derived._Quad
--*/
{
  /* Validating field _34 */
  return BaseValidatePair(Input);
}

uint64_t DerivedValidateQuad(EverParseInputBuffer Input)
{
  /* Field _Quad__12 */
  uint64_t resultAfter12 = ValidateQuad12(Input);
  if (EverParseIsError(resultAfter12))
  {
    return resultAfter12;
  }
  /* Field _Quad__34 */
  return ValidateQuad34(Input);
}

