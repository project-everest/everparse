

#include "Derived.h"

static inline uint64_t
ValidateTriplePair(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _Triple_pair
        of type Derived._Triple
--*/
{
  /* SNIPPET_START: Triple */
  uint64_t positionAfterTriple = BaseValidatePair(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterTriple))
  {
    return positionAfterTriple;
  }
  Err("_Triple",
    "_Triple_pair",
    EverParseErrorReasonOfResult(positionAfterTriple),
    Ctxt,
    Input,
    Pos);
  return positionAfterTriple;
}

static inline uint64_t
ValidateTripleThird(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _Triple_third
        of type Derived._Triple
--*/
{
  /* Validating field third */
  uint64_t positionAfterTriple = BaseValidateUlong(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterTriple))
  {
    return positionAfterTriple;
  }
  Err("_Triple",
    "_Triple_third",
    EverParseErrorReasonOfResult(positionAfterTriple),
    Ctxt,
    Input,
    Pos);
  return positionAfterTriple;
}

uint64_t
DerivedValidateTriple(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
{
  /* Field _Triple_pair */
  uint64_t positionAfterTriple = ValidateTriplePair(Ctxt, Err, Input, Pos);
  uint64_t positionAfterpair;
  if (EverParseIsSuccess(positionAfterTriple))
  {
    positionAfterpair = positionAfterTriple;
  }
  else
  {
    Err("_Triple", "pair", EverParseErrorReasonOfResult(positionAfterTriple), Ctxt, Input, Pos);
    positionAfterpair = positionAfterTriple;
  }
  if (EverParseIsError(positionAfterpair))
  {
    return positionAfterpair;
  }
  /* Field _Triple_third */
  uint64_t positionAfterTriple0 = ValidateTripleThird(Ctxt, Err, Input, positionAfterpair);
  if (EverParseIsSuccess(positionAfterTriple0))
  {
    return positionAfterTriple0;
  }
  Err("_Triple",
    "third",
    EverParseErrorReasonOfResult(positionAfterTriple0),
    Ctxt,
    Input,
    positionAfterpair);
  return positionAfterTriple0;
}

static inline uint64_t
ValidateQuad12(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _Quad__12
        of type Derived._Quad
--*/
{
  /* Validating field _12 */
  uint64_t positionAfterQuad = BaseValidatePair(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterQuad))
  {
    return positionAfterQuad;
  }
  Err("_Quad", "_Quad__12", EverParseErrorReasonOfResult(positionAfterQuad), Ctxt, Input, Pos);
  return positionAfterQuad;
}

static inline uint64_t
ValidateQuad34(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
/*++
    Internal helper function:
        Validator for field _Quad__34
        of type Derived._Quad
--*/
{
  /* Validating field _34 */
  uint64_t positionAfterQuad = BaseValidatePair(Ctxt, Err, Input, Pos);
  if (EverParseIsSuccess(positionAfterQuad))
  {
    return positionAfterQuad;
  }
  Err("_Quad", "_Quad__34", EverParseErrorReasonOfResult(positionAfterQuad), Ctxt, Input, Pos);
  return positionAfterQuad;
}

uint64_t
DerivedValidateQuad(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    EverParseInputBuffer x4,
    uint64_t x5
  ),
  EverParseInputBuffer Input,
  uint64_t Pos
)
{
  /* Field _Quad__12 */
  uint64_t positionAfterQuad = ValidateQuad12(Ctxt, Err, Input, Pos);
  uint64_t positionAfter12;
  if (EverParseIsSuccess(positionAfterQuad))
  {
    positionAfter12 = positionAfterQuad;
  }
  else
  {
    Err("_Quad", "_12", EverParseErrorReasonOfResult(positionAfterQuad), Ctxt, Input, Pos);
    positionAfter12 = positionAfterQuad;
  }
  if (EverParseIsError(positionAfter12))
  {
    return positionAfter12;
  }
  /* Field _Quad__34 */
  uint64_t positionAfterQuad0 = ValidateQuad34(Ctxt, Err, Input, positionAfter12);
  if (EverParseIsSuccess(positionAfterQuad0))
  {
    return positionAfterQuad0;
  }
  Err("_Quad",
    "_34",
    EverParseErrorReasonOfResult(positionAfterQuad0),
    Ctxt,
    Input,
    positionAfter12);
  return positionAfterQuad0;
}

