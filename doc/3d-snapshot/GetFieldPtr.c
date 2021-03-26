

#include "GetFieldPtr.h"

/*
Auto-generated field identifier for error reporting
*/
#define GETFIELDPTR__T__F1 ((uint64_t)29U)

/*
Auto-generated field identifier for error reporting
*/
#define GETFIELDPTR__T__F2 ((uint64_t)30U)

static inline uint64_t ValidateTF1(uint32_t InputLength, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _T_f1
        of type GetFieldPtr._T
--*/
{
  /* SNIPPET_START: GetFieldPtr.T */
  uint64_t endPositionOrError;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)(uint32_t)(uint8_t)10U)
  {
    endPositionOrError = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    endPositionOrError = StartPosition + (uint64_t)(uint32_t)(uint8_t)10U;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, GETFIELDPTR__T__F1);
}

static inline uint64_t
ValidateTF2(uint8_t **Out, uint32_t InputLength, uint8_t *Input, uint64_t StartPosition)
/*++
    Internal helper function:
        Validator for field _T_f2
        of type GetFieldPtr._T
--*/
{
  /* Validating field f2 */
  uint64_t positionAfterTF2;
  if (((uint64_t)InputLength - StartPosition) < (uint64_t)(uint32_t)(uint8_t)20U)
  {
    positionAfterTF2 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterTF2 = StartPosition + (uint64_t)(uint32_t)(uint8_t)20U;
  }
  uint64_t endPositionOrError;
  if (EverParseIsSuccess(positionAfterTF2))
  {
    uint8_t *base = Input;
    uint8_t *x = base + (uint32_t)StartPosition;
    *Out = x;
    BOOLEAN actionSuccessTF2 = TRUE;
    if (!actionSuccessTF2)
    {
      endPositionOrError = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      endPositionOrError = positionAfterTF2;
    }
  }
  else
  {
    endPositionOrError = positionAfterTF2;
  }
  return EverParseMaybeSetErrorCode(endPositionOrError, StartPosition, GETFIELDPTR__T__F2);
}

uint64_t
GetFieldPtrValidateT(uint8_t **Out, uint32_t Uu, uint8_t *Input, uint64_t StartPosition)
{
  /* Field _T_f1 */
  uint64_t positionAfterf1 = ValidateTF1(Uu, StartPosition);
  if (EverParseIsError(positionAfterf1))
  {
    return positionAfterf1;
  }
  /* Field _T_f2 */
  return ValidateTF2(Out, Uu, Input, positionAfterf1);
}

