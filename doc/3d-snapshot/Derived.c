

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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _Triple_pair
        of type Derived._Triple
--*/
{
  /* SNIPPET_START: Triple */
  uint32_t positionBeforeTriple = *Input.pos;
  uint64_t resultAfterTriple = BaseValidatePair(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterTriple))
  {
    return resultAfterTriple;
  }
  Err("_Triple",
    "_Triple_pair",
    EverParseErrorReasonOfResult(resultAfterTriple),
    Ctxt,
    Input,
    positionBeforeTriple);
  return resultAfterTriple;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _Triple_third
        of type Derived._Triple
--*/
{
  /* Validating field third */
  uint32_t positionBeforeTriple = *Input.pos;
  uint64_t resultAfterTriple = BaseValidateUlong(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterTriple))
  {
    return resultAfterTriple;
  }
  Err("_Triple",
    "_Triple_third",
    EverParseErrorReasonOfResult(resultAfterTriple),
    Ctxt,
    Input,
    positionBeforeTriple);
  return resultAfterTriple;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
{
  /* Field _Triple_pair */
  uint32_t positionBeforeTriple = *Input.pos;
  uint64_t resultAfterTriple = ValidateTriplePair(Ctxt, Err, Input);
  uint64_t resultAfterpair;
  if (EverParseIsSuccess(resultAfterTriple))
  {
    resultAfterpair = resultAfterTriple;
  }
  else
  {
    Err("_Triple",
      "pair",
      EverParseErrorReasonOfResult(resultAfterTriple),
      Ctxt,
      Input,
      positionBeforeTriple);
    resultAfterpair = resultAfterTriple;
  }
  if (EverParseIsError(resultAfterpair))
  {
    return resultAfterpair;
  }
  /* Field _Triple_third */
  uint32_t positionBeforeTriple0 = *Input.pos;
  uint64_t resultAfterTriple0 = ValidateTripleThird(Ctxt, Err, Input);
  uint64_t res;
  if (EverParseIsSuccess(resultAfterTriple0))
  {
    res = resultAfterTriple0;
  }
  else
  {
    Err("_Triple",
      "third",
      EverParseErrorReasonOfResult(resultAfterTriple0),
      Ctxt,
      Input,
      positionBeforeTriple0);
    res = resultAfterTriple0;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  return res;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _Quad__12
        of type Derived._Quad
--*/
{
  /* Validating field _12 */
  uint32_t positionBeforeQuad = *Input.pos;
  uint64_t resultAfterQuad = BaseValidatePair(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterQuad))
  {
    return resultAfterQuad;
  }
  Err("_Quad",
    "_Quad__12",
    EverParseErrorReasonOfResult(resultAfterQuad),
    Ctxt,
    Input,
    positionBeforeQuad);
  return resultAfterQuad;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
/*++
    Internal helper function:
        Validator for field _Quad__34
        of type Derived._Quad
--*/
{
  /* Validating field _34 */
  uint32_t positionBeforeQuad = *Input.pos;
  uint64_t resultAfterQuad = BaseValidatePair(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterQuad))
  {
    return resultAfterQuad;
  }
  Err("_Quad",
    "_Quad__34",
    EverParseErrorReasonOfResult(resultAfterQuad),
    Ctxt,
    Input,
    positionBeforeQuad);
  return resultAfterQuad;
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
    uint32_t x5
  ),
  EverParseInputBuffer Input
)
{
  /* Field _Quad__12 */
  uint32_t positionBeforeQuad = *Input.pos;
  uint64_t resultAfterQuad = ValidateQuad12(Ctxt, Err, Input);
  uint64_t resultAfter12;
  if (EverParseIsSuccess(resultAfterQuad))
  {
    resultAfter12 = resultAfterQuad;
  }
  else
  {
    Err("_Quad",
      "_12",
      EverParseErrorReasonOfResult(resultAfterQuad),
      Ctxt,
      Input,
      positionBeforeQuad);
    resultAfter12 = resultAfterQuad;
  }
  if (EverParseIsError(resultAfter12))
  {
    return resultAfter12;
  }
  /* Field _Quad__34 */
  uint32_t positionBeforeQuad0 = *Input.pos;
  uint64_t resultAfterQuad0 = ValidateQuad34(Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterQuad0))
  {
    return resultAfterQuad0;
  }
  Err("_Quad",
    "_34",
    EverParseErrorReasonOfResult(resultAfterQuad0),
    Ctxt,
    Input,
    positionBeforeQuad0);
  return resultAfterQuad0;
}

