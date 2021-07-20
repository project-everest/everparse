

#include "GetFieldPtr.h"

/*
Auto-generated field identifier for error reporting
*/
#define GETFIELDPTR__T__F1 ((uint64_t)29U)

/*
Auto-generated field identifier for error reporting
*/
#define GETFIELDPTR__T__F2 ((uint64_t)30U)

static inline uint64_t ValidateTF1(EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _T_f1
        of type GetFieldPtr._T
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* SNIPPET_START: GetFieldPtr.T */
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
  uint64_t result = res;
  return EverParseMaybeSetErrorCode(result, startPosition1, GETFIELDPTR__T__F1);
}

static inline uint64_t ValidateTF2(uint8_t **Out, EverParseInputBuffer Input)
/*++
    Internal helper function:
        Validator for field _T_f2
        of type GetFieldPtr._T
--*/
{
  uint32_t startPosition = *Input.pos;
  uint64_t startPosition1 = (uint64_t)startPosition;
  /* Validating field f2 */
  uint32_t positionBeforeTF2 = *Input.pos;
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
  uint64_t resultAfterTF2 = res;
  uint64_t result;
  if (EverParseIsSuccess(resultAfterTF2))
  {
    uint8_t *x = Input.buf + positionBeforeTF2;
    *Out = x;
    BOOLEAN actionSuccessTF2 = TRUE;
    if (!actionSuccessTF2)
    {
      result = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      result = resultAfterTF2;
    }
  }
  else
  {
    result = resultAfterTF2;
  }
  return EverParseMaybeSetErrorCode(result, startPosition1, GETFIELDPTR__T__F2);
}

uint64_t GetFieldPtrValidateT(uint8_t **Out, EverParseInputBuffer Input)
{
  /* Field _T_f1 */
  uint64_t resultAfterf1 = ValidateTF1(Input);
  if (EverParseIsError(resultAfterf1))
  {
    return resultAfterf1;
  }
  /* Field _T_f2 */
  return ValidateTF2(Out, Input);
}

