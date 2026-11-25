#include "Color.h"

static uint8_t ColorValidateColoredPointCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t ColorValidateColoredPointCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  /* Validating field col */
  size_t currentPosition = slPos[0];
  uint64_t fieldStartColoredPoint = (uint64_t)currentPosition;
  size_t offsetInColRefinement = 0;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t offsetBeforeColRefinement = offsetInColRefinement;
  size_t positionBeforeColRefinement = slPos[0];
  size_t bytesRemainingBeforeColRefinement = (slLen - positionBeforeColRefinement);
  bool hasBytesForColRefinement;
  if (offsetBeforeColRefinement <= bytesRemainingBeforeColRefinement) {
    hasBytesForColRefinement = (4 <= (bytesRemainingBeforeColRefinement - offsetBeforeColRefinement));
  }
  else {
    hasBytesForColRefinement = false;
  }
  uint8_t resultAfterColRefinement;
  if (hasBytesForColRefinement) {
    offsetInColRefinement = (offsetBeforeColRefinement + 4);
    resultAfterColRefinement = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterColRefinement = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterColoredPoint;
  if (resultAfterColRefinement == EVERPARSE_STATUS_SUCCESS) {
    /* reading field_value */
    size_t positionOfColRefinement = slPos[0];
    size_t positionAfterColRefinement = (positionOfColRefinement + 4);
    uint8_t *bytesOfColRefinement = (slBase + positionOfColRefinement);
    slPos[0] = positionAfterColRefinement;
    uint32_t colRefinement = EverParse3dReadUint32(bytesOfColRefinement);
    /* start: checking constraint */
    bool colRefinementConstraintIsOk = ((COLOR_RED == colRefinement) || ((COLOR_GREEN == colRefinement) || (COLOR_BLUE == colRefinement)));
    /* end: checking constraint */
    if (colRefinementConstraintIsOk) {
      resultAfterColoredPoint = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterColoredPoint = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
    }
  }
  else {
    resultAfterColoredPoint = resultAfterColRefinement;
  }
  uint8_t resultAfterColRefinement1;
  if (resultAfterColoredPoint == EVERPARSE_STATUS_SUCCESS) {
    resultAfterColRefinement1 = resultAfterColoredPoint;
  }
  else {
    (void)(errorHandlerFn("_coloredPoint", "col.refinement", EverParse3dErrorReasonOfResult(resultAfterColoredPoint), EverParse3dLegacyKind(resultAfterColoredPoint), ctxt, slBase, fieldStartColoredPoint));
    resultAfterColRefinement1 = resultAfterColoredPoint;
  }
  if (resultAfterColRefinement1 == EVERPARSE_STATUS_SUCCESS) {
    size_t currentPosition1 = slPos[0];
    uint64_t fieldStartColoredPoint1 = (uint64_t)currentPosition1;
    size_t scanOffset = 0;
    size_t offsetBeforeX = scanOffset;
    size_t positionBeforeX = slPos[0];
    size_t bytesRemainingBeforeX = (slLen - positionBeforeX);
    bool hasBytesForX;
    if (offsetBeforeX <= bytesRemainingBeforeX) {
      hasBytesForX = ((size_t)8 <= (bytesRemainingBeforeX - offsetBeforeX));
    }
    else {
      hasBytesForX = false;
    }
    uint8_t res;
    if (hasBytesForX) {
      scanOffset = (offsetBeforeX + (size_t)8);
      res = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      res = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterColoredPoint1;
    if (res == EVERPARSE_STATUS_SUCCESS) {
      size_t currentPosition2 = slPos[0];
      size_t newPosition = (currentPosition2 + scanOffset);
      slPos[0] = newPosition;
      resultAfterColoredPoint1 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterColoredPoint1 = res;
    }
    if (resultAfterColoredPoint1 == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterColoredPoint1;
    }
    else {
      (void)(errorHandlerFn("_coloredPoint", "x", EverParse3dErrorReasonOfResult(resultAfterColoredPoint1), EverParse3dLegacyKind(resultAfterColoredPoint1), ctxt, slBase, fieldStartColoredPoint1));
      return resultAfterColoredPoint1;
    }
  }
  else {
    return resultAfterColRefinement1;
  }
}

uint64_t ColorValidateColoredPoint(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = ColorValidateColoredPointCore(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * EVERPARSE_VALIDATOR_ERROR_GENERIC) + position);
}


