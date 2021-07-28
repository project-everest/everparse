

#include "GetFieldPtr.h"

static inline uint64_t
ValidateTF1(
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
        Validator for field _T_f1
        of type GetFieldPtr._T
--*/
{
  /* SNIPPET_START: GetFieldPtr.T */
  uint32_t positionBeforeT = *Input.pos;
  uint32_t currentPosition0 = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)(uint8_t)10U <= (Input.len - currentPosition0);
  uint64_t res;
  if (hasBytes)
  {
    res = (uint64_t)(uint32_t)(uint8_t)10U;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  uint64_t resultAfterT = res;
  if (EverParseIsSuccess(resultAfterT))
  {
    return resultAfterT;
  }
  Err("_T", "_T_f1", EverParseErrorReasonOfResult(resultAfterT), Ctxt, Input, positionBeforeT);
  return resultAfterT;
}

static inline uint64_t
ValidateTF2(
  uint8_t **Out,
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
        Validator for field _T_f2
        of type GetFieldPtr._T
--*/
{
  /* Validating field f2 */
  uint32_t positionBeforeT = *Input.pos;
  uint32_t positionBeforeT1 = *Input.pos;
  uint32_t positionBeforeT2 = *Input.pos;
  uint32_t currentPosition0 = *Input.pos;
  BOOLEAN hasBytes = (uint32_t)(uint8_t)20U <= (Input.len - currentPosition0);
  uint64_t res;
  if (hasBytes)
  {
    res = (uint64_t)(uint32_t)(uint8_t)20U;
  }
  else
  {
    res = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  if (EverParseIsSuccess(res))
  {
    uint32_t currentPosition = *Input.pos;
    *Input.pos = currentPosition + (uint32_t)res;
  }
  uint64_t resultAfterT = res;
  uint64_t resultAfterT0;
  if (EverParseIsSuccess(resultAfterT))
  {
    resultAfterT0 = resultAfterT;
  }
  else
  {
    Err("_T",
      "_T_f2.base",
      EverParseErrorReasonOfResult(resultAfterT),
      Ctxt,
      Input,
      positionBeforeT2);
    resultAfterT0 = resultAfterT;
  }
  uint64_t resultAfterT1;
  if (EverParseIsSuccess(resultAfterT0))
  {
    uint8_t *x = Input.buf + positionBeforeT1;
    *Out = x;
    BOOLEAN actionSuccessT = TRUE;
    if (!actionSuccessT)
    {
      resultAfterT1 = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      resultAfterT1 = resultAfterT0;
    }
  }
  else
  {
    resultAfterT1 = resultAfterT0;
  }
  if (EverParseIsSuccess(resultAfterT1))
  {
    return resultAfterT1;
  }
  Err("_T", "_T_f2", EverParseErrorReasonOfResult(resultAfterT1), Ctxt, Input, positionBeforeT);
  return resultAfterT1;
}

uint64_t
GetFieldPtrValidateT(
  uint8_t **Out,
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
  /* Field _T_f1 */
  uint32_t positionBeforeT = *Input.pos;
  uint64_t resultAfterT = ValidateTF1(Ctxt, Err, Input);
  uint64_t resultAfterf1;
  if (EverParseIsSuccess(resultAfterT))
  {
    resultAfterf1 = resultAfterT;
  }
  else
  {
    Err("_T", "f1", EverParseErrorReasonOfResult(resultAfterT), Ctxt, Input, positionBeforeT);
    resultAfterf1 = resultAfterT;
  }
  if (EverParseIsError(resultAfterf1))
  {
    return resultAfterf1;
  }
  /* Field _T_f2 */
  uint32_t positionBeforeT0 = *Input.pos;
  uint64_t resultAfterT0 = ValidateTF2(Out, Ctxt, Err, Input);
  if (EverParseIsSuccess(resultAfterT0))
  {
    return resultAfterT0;
  }
  Err("_T", "f2", EverParseErrorReasonOfResult(resultAfterT0), Ctxt, Input, positionBeforeT0);
  return resultAfterT0;
}

