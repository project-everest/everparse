

#include "Derived.h"

/*
Auto-generated field identifier for error reporting
*/
#define DERIVED__TRIPLE__THIRD ((uint64_t)26U)

static inline uint64_t
ValidateTriplePair(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Triple_pair
        of type Derived._Triple
--*/
{
  /* SNIPPET_START: Triple */
  return BaseValidatePair(InputLength, Input, StartPosition);
}

static inline uint64_t
ValidateTripleThird(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Triple_third
        of type Derived._Triple
--*/
{
  /* Validating field third */
  uint64_t endPositionOrError = BaseValidateUlong(InputLength, Input, StartPosition);
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, DERIVED__TRIPLE__THIRD);
}

uint64_t DerivedValidateTriple(uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _Triple_pair */
  uint64_t positionAfterpair = ValidateTriplePair(Uu, Input, StartPosition);
  if (EverParseIsError(positionAfterpair))
  {
    return positionAfterpair;
  }
  /* Field _Triple_third */
  return ValidateTripleThird(Uu, Input, positionAfterpair);
}

static inline uint64_t
ValidateQuad12(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Quad__12
        of type Derived._Quad
--*/
{
  /* Validating field _12 */
  return BaseValidatePair(InputLength, Input, StartPosition);
}

static inline uint64_t
ValidateQuad34(uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _Quad__34
        of type Derived._Quad
--*/
{
  /* Validating field _34 */
  return BaseValidatePair(InputLength, Input, StartPosition);
}

uint64_t DerivedValidateQuad(uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _Quad__12 */
  uint64_t positionAfter12 = ValidateQuad12(Uu, Input, StartPosition);
  if (EverParseIsError(positionAfter12))
  {
    return positionAfter12;
  }
  /* Field _Quad__34 */
  return ValidateQuad34(Uu, Input, positionAfter12);
}

