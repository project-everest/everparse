#include "EnumConstraint.h"

static uint8_t EnumConstraintValidateEnumConstraintCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t EnumConstraintValidateEnumConstraintCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartEnumConstraint = (uint64_t)currentPosition;
  size_t offsetInCol = 0;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t offsetBeforeCol = offsetInCol;
  size_t positionBeforeCol = slPos[0];
  size_t bytesRemainingBeforeCol = (slLen - positionBeforeCol);
  bool hasBytesForCol;
  if (offsetBeforeCol <= bytesRemainingBeforeCol) {
    hasBytesForCol = (4 <= (bytesRemainingBeforeCol - offsetBeforeCol));
  }
  else {
    hasBytesForCol = false;
  }
  uint8_t resultAfterCol;
  if (hasBytesForCol) {
    offsetInCol = (offsetBeforeCol + 4);
    resultAfterCol = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterCol = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterEnumConstraint;
  if (resultAfterCol == EVERPARSE_STATUS_SUCCESS) {
    size_t positionOfCol = slPos[0];
    size_t positionAfterCol = (positionOfCol + 4);
    uint8_t *bytesOfCol = (slBase + positionOfCol);
    slPos[0] = positionAfterCol;
    uint32_t col = EverParse3dReadUint32(bytesOfCol);
    bool colConstraintIsOk = (((col == ENUMCONSTRAINT_RED) || (col == ENUMCONSTRAINT_GREEN)) || (col == ENUMCONSTRAINT_BLUE));
    if (colConstraintIsOk) {
      /* Validating field x */
      size_t currentPosition1 = slPos[0];
      uint64_t fieldStartEnumConstraint1 = (uint64_t)currentPosition1;
      size_t offsetInXRefinement = 0;
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      size_t offsetBeforeXRefinement = offsetInXRefinement;
      size_t positionBeforeXRefinement = slPos[0];
      size_t bytesRemainingBeforeXRefinement = (slLen - positionBeforeXRefinement);
      bool hasBytesForXRefinement;
      if (offsetBeforeXRefinement <= bytesRemainingBeforeXRefinement) {
        hasBytesForXRefinement = (4 <= (bytesRemainingBeforeXRefinement - offsetBeforeXRefinement));
      }
      else {
        hasBytesForXRefinement = false;
      }
      uint8_t resultAfterXRefinement;
      if (hasBytesForXRefinement) {
        offsetInXRefinement = (offsetBeforeXRefinement + 4);
        resultAfterXRefinement = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultAfterXRefinement = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
      }
      uint8_t resultAfterEnumConstraint_1;
      if (resultAfterXRefinement == EVERPARSE_STATUS_SUCCESS) {
        /* reading field_value */
        size_t positionOfXRefinement = slPos[0];
        size_t positionAfterXRefinement = (positionOfXRefinement + 4);
        uint8_t *bytesOfXRefinement = (slBase + positionOfXRefinement);
        slPos[0] = positionAfterXRefinement;
        uint32_t xRefinement = EverParse3dReadUint32(bytesOfXRefinement);
        /* start: checking constraint */
        bool xRefinementConstraintIsOk = ((xRefinement == (uint32_t)0) || (col == ENUMCONSTRAINT_GREEN));
        /* end: checking constraint */
        if (xRefinementConstraintIsOk) {
          resultAfterEnumConstraint_1 = EVERPARSE_STATUS_SUCCESS;
        }
        else {
          resultAfterEnumConstraint_1 = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
        }
      }
      else {
        resultAfterEnumConstraint_1 = resultAfterXRefinement;
      }
      if (resultAfterEnumConstraint_1 == EVERPARSE_STATUS_SUCCESS) {
        resultAfterEnumConstraint = resultAfterEnumConstraint_1;
      }
      else {
        (void)(errorHandlerFn("_enum_constraint", "x.refinement", EverParse3dErrorReasonOfResult(resultAfterEnumConstraint_1), EverParse3dLegacyKind(resultAfterEnumConstraint_1), ctxt, slBase, fieldStartEnumConstraint1));
        resultAfterEnumConstraint = resultAfterEnumConstraint_1;
      }
    }
    else {
      resultAfterEnumConstraint = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
    }
  }
  else {
    resultAfterEnumConstraint = resultAfterCol;
  }
  if (resultAfterEnumConstraint == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterEnumConstraint;
  }
  else {
    (void)(errorHandlerFn("_enum_constraint", "col", EverParse3dErrorReasonOfResult(resultAfterEnumConstraint), EverParse3dLegacyKind(resultAfterEnumConstraint), ctxt, slBase, fieldStartEnumConstraint));
    return resultAfterEnumConstraint;
  }
}

uint64_t EnumConstraintValidateEnumConstraint(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = EnumConstraintValidateEnumConstraintCore(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * EVERPARSE_VALIDATOR_ERROR_GENERIC) + position);
}


