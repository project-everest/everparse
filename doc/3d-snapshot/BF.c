

#include "BF.h"

uint64_t
BfValidateBf(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field __bitfield_0 */
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  BOOLEAN hasBytes = (uint64_t)4U <= (InputLength - StartPosition);
  uint64_t positionAfterBitfield0_refinement;
  if (hasBytes)
  {
    positionAfterBitfield0_refinement = StartPosition + (uint64_t)4U;
  }
  else
  {
    positionAfterBitfield0_refinement =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t positionAfterBf;
  if (EverParseIsError(positionAfterBitfield0_refinement))
  {
    positionAfterBf = positionAfterBitfield0_refinement;
  }
  else
  {
    /* reading field_value */
    uint32_t bitfield0_refinement = Load32Le(Input + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN
    bitfield0_refinementConstraintIsOk =
      EverParseGetBitfield32(bitfield0_refinement,
        (uint32_t)6U,
        (uint32_t)16U)
      <= (uint32_t)(uint16_t)900U
      &&
        (EverParseGetBitfield32(bitfield0_refinement,
          (uint32_t)6U,
          (uint32_t)16U)
        + EverParseGetBitfield32(bitfield0_refinement, (uint32_t)16U, (uint32_t)32U))
        <= (uint32_t)(uint16_t)60000U;
    /* end: checking constraint */
    positionAfterBf =
      EverParseCheckConstraintOk(bitfield0_refinementConstraintIsOk,
        positionAfterBitfield0_refinement);
  }
  if (EverParseIsSuccess(positionAfterBf))
  {
    return positionAfterBf;
  }
  Err("_BF",
    "__bitfield_0.refinement",
    EverParseErrorReasonOfResult(positionAfterBf),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterBf;
}

uint64_t
BfValidateBf2(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field __bitfield_0 */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (uint64_t)2U <= (InputLength - StartPosition);
  uint64_t positionAfterBf2;
  if (hasBytes0)
  {
    positionAfterBf2 = StartPosition + (uint64_t)2U;
  }
  else
  {
    positionAfterBf2 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterBf2))
  {
    res0 = positionAfterBf2;
  }
  else
  {
    Err("_BF2",
      "__bitfield_0",
      EverParseErrorReasonOfResult(positionAfterBf2),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterBf2;
  }
  uint64_t positionAfterBitfield0 = res0;
  if (EverParseIsError(positionAfterBitfield0))
  {
    return positionAfterBitfield0;
  }
  /* Validating field __bitfield_1 */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  BOOLEAN hasBytes1 = (uint64_t)2U <= (InputLength - positionAfterBitfield0);
  uint64_t positionAfterBf20;
  if (hasBytes1)
  {
    positionAfterBf20 = positionAfterBitfield0 + (uint64_t)2U;
  }
  else
  {
    positionAfterBf20 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBitfield0);
  }
  uint64_t res;
  if (EverParseIsSuccess(positionAfterBf20))
  {
    res = positionAfterBf20;
  }
  else
  {
    Err("_BF2",
      "__bitfield_1",
      EverParseErrorReasonOfResult(positionAfterBf20),
      Ctxt,
      Input,
      positionAfterBitfield0);
    res = positionAfterBf20;
  }
  uint64_t positionAfterBitfield1 = res;
  if (EverParseIsError(positionAfterBitfield1))
  {
    return positionAfterBitfield1;
  }
  /* Validating field z */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes = (uint64_t)1U <= (InputLength - positionAfterBitfield1);
  uint64_t positionAfterBf21;
  if (hasBytes)
  {
    positionAfterBf21 = positionAfterBitfield1 + (uint64_t)1U;
  }
  else
  {
    positionAfterBf21 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterBitfield1);
  }
  if (EverParseIsSuccess(positionAfterBf21))
  {
    return positionAfterBf21;
  }
  Err("_BF2",
    "z",
    EverParseErrorReasonOfResult(positionAfterBf21),
    Ctxt,
    Input,
    positionAfterBitfield1);
  return positionAfterBf21;
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
    uint8_t *x4,
    uint64_t x5
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field emp */
  uint64_t positionAfterDummy = StartPosition;
  if (EverParseIsSuccess(positionAfterDummy))
  {
    return positionAfterDummy;
  }
  Err("_dummy",
    "emp",
    EverParseErrorReasonOfResult(positionAfterDummy),
    Ctxt,
    Input,
    StartPosition);
  return positionAfterDummy;
}

