#include "GetFieldPtr.h"

static uint8_t GetFieldPtrValidateTCore(uint8_t **out, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static uint8_t GetFieldPtrValidateTactCore(uint8_t **out, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t GetFieldPtrValidateTCore(uint8_t **out, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  /* Validating field f1 */
  size_t currentPosition = slPos[0];
  uint64_t fieldStartT = (uint64_t)currentPosition;
  size_t scanOffset = 0;
  size_t offsetBefore = scanOffset;
  size_t positionBefore = slPos[0];
  size_t bytesRemainingBefore = (slLen - positionBefore);
  bool hasBytesFor;
  if (offsetBefore <= bytesRemainingBefore) {
    hasBytesFor = ((size_t)10 <= (bytesRemainingBefore - offsetBefore));
  }
  else {
    hasBytesFor = false;
  }
  uint8_t res;
  if (hasBytesFor) {
    scanOffset = (offsetBefore + (size_t)10);
    res = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    res = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterT;
  if (res == EVERPARSE_STATUS_SUCCESS) {
    size_t currentPosition1 = slPos[0];
    size_t newPosition = (currentPosition1 + scanOffset);
    slPos[0] = newPosition;
    resultAfterT = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterT = res;
  }
  uint8_t resultAfterF1;
  if (resultAfterT == EVERPARSE_STATUS_SUCCESS) {
    resultAfterF1 = resultAfterT;
  }
  else {
    (void)(errorHandlerFn("_T", "f1", EverParse3dErrorReasonOfResult(resultAfterT), EverParse3dLegacyKind(resultAfterT), ctxt, slBase, fieldStartT));
    resultAfterF1 = resultAfterT;
  }
  if (resultAfterF1 == EVERPARSE_STATUS_SUCCESS) {
    /* Validating field f2 */
    size_t currentPosition1_1 = slPos[0];
    uint64_t fieldStartT1 = (uint64_t)currentPosition1_1;
    size_t currentPosition2 = slPos[0];
    uint64_t fieldStartF2 = (uint64_t)currentPosition2;
    size_t currentPosition3 = slPos[0];
    uint64_t fieldStartT2 = (uint64_t)currentPosition3;
    size_t scanOffset1 = 0;
    size_t offsetBefore1 = scanOffset1;
    size_t positionBefore1 = slPos[0];
    size_t bytesRemainingBefore1 = (slLen - positionBefore1);
    bool hasBytesFor1;
    if (offsetBefore1 <= bytesRemainingBefore1) {
      hasBytesFor1 = ((size_t)20 <= (bytesRemainingBefore1 - offsetBefore1));
    }
    else {
      hasBytesFor1 = false;
    }
    uint8_t res1;
    if (hasBytesFor1) {
      scanOffset1 = (offsetBefore1 + (size_t)20);
      res1 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      res1 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterT1;
    if (res1 == EVERPARSE_STATUS_SUCCESS) {
      size_t currentPosition4 = slPos[0];
      size_t newPosition_1 = (currentPosition4 + scanOffset1);
      slPos[0] = newPosition_1;
      resultAfterT1 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterT1 = res1;
    }
    uint8_t resultAfterF2;
    if (resultAfterT1 == EVERPARSE_STATUS_SUCCESS) {
      resultAfterF2 = resultAfterT1;
    }
    else {
      (void)(errorHandlerFn("_T", "f2.base", EverParse3dErrorReasonOfResult(resultAfterT1), EverParse3dLegacyKind(resultAfterT1), ctxt, slBase, fieldStartT2));
      resultAfterF2 = resultAfterT1;
    }
    uint8_t resultAfterT2;
    if (resultAfterF2 == EVERPARSE_STATUS_SUCCESS) {
      size_t startPosSz = (size_t)fieldStartF2;
      uint8_t *hd = (slBase + startPosSz);
      out[0] = hd;
      if (true) {
        resultAfterT2 = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultAfterT2 = EVERPARSE_STATUS_ERROR_ACTION_FAILED;
      }
    }
    else {
      resultAfterT2 = resultAfterF2;
    }
    if (resultAfterT2 == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterT2;
    }
    else {
      (void)(errorHandlerFn("_T", "f2", EverParse3dErrorReasonOfResult(resultAfterT2), EverParse3dLegacyKind(resultAfterT2), ctxt, slBase, fieldStartT1));
      return resultAfterT2;
    }
  }
  else {
    return resultAfterF1;
  }
}

uint64_t GetFieldPtrValidateT(uint8_t **out, uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = GetFieldPtrValidateTCore(out, ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * EVERPARSE_VALIDATOR_ERROR_GENERIC) + position);
}

static uint8_t GetFieldPtrValidateTactCore(uint8_t **out, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  /* Validating field f1 */
  size_t currentPosition = slPos[0];
  uint64_t fieldStartTact = (uint64_t)currentPosition;
  size_t scanOffset = 0;
  size_t offsetBefore = scanOffset;
  size_t positionBefore = slPos[0];
  size_t bytesRemainingBefore = (slLen - positionBefore);
  bool hasBytesFor;
  if (offsetBefore <= bytesRemainingBefore) {
    hasBytesFor = ((size_t)10 <= (bytesRemainingBefore - offsetBefore));
  }
  else {
    hasBytesFor = false;
  }
  uint8_t res;
  if (hasBytesFor) {
    scanOffset = (offsetBefore + (size_t)10);
    res = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    res = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterTact;
  if (res == EVERPARSE_STATUS_SUCCESS) {
    size_t currentPosition1 = slPos[0];
    size_t newPosition = (currentPosition1 + scanOffset);
    slPos[0] = newPosition;
    resultAfterTact = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterTact = res;
  }
  uint8_t resultAfterF1;
  if (resultAfterTact == EVERPARSE_STATUS_SUCCESS) {
    resultAfterF1 = resultAfterTact;
  }
  else {
    (void)(errorHandlerFn("_TAct", "f1", EverParse3dErrorReasonOfResult(resultAfterTact), EverParse3dLegacyKind(resultAfterTact), ctxt, slBase, fieldStartTact));
    resultAfterF1 = resultAfterTact;
  }
  if (resultAfterF1 == EVERPARSE_STATUS_SUCCESS) {
    /* Validating field f2 */
    size_t currentPosition1_1 = slPos[0];
    uint64_t fieldStartTact1 = (uint64_t)currentPosition1_1;
    size_t currentPosition2 = slPos[0];
    uint64_t fieldStartF2 = (uint64_t)currentPosition2;
    size_t currentPosition3 = slPos[0];
    uint64_t fieldStartTact2 = (uint64_t)currentPosition3;
    size_t scanOffset1 = 0;
    size_t offsetBefore1 = scanOffset1;
    size_t positionBefore1 = slPos[0];
    size_t bytesRemainingBefore1 = (slLen - positionBefore1);
    bool hasBytesFor1;
    if (offsetBefore1 <= bytesRemainingBefore1) {
      hasBytesFor1 = ((size_t)20 <= (bytesRemainingBefore1 - offsetBefore1));
    }
    else {
      hasBytesFor1 = false;
    }
    uint8_t res1;
    if (hasBytesFor1) {
      scanOffset1 = (offsetBefore1 + (size_t)20);
      res1 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      res1 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterTact1;
    if (res1 == EVERPARSE_STATUS_SUCCESS) {
      size_t currentPosition4 = slPos[0];
      size_t newPosition_1 = (currentPosition4 + scanOffset1);
      slPos[0] = newPosition_1;
      resultAfterTact1 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterTact1 = res1;
    }
    uint8_t resultAfterF2;
    if (resultAfterTact1 == EVERPARSE_STATUS_SUCCESS) {
      resultAfterF2 = resultAfterTact1;
    }
    else {
      (void)(errorHandlerFn("_TAct", "f2.base", EverParse3dErrorReasonOfResult(resultAfterTact1), EverParse3dLegacyKind(resultAfterTact1), ctxt, slBase, fieldStartTact2));
      resultAfterF2 = resultAfterTact1;
    }
    uint8_t resultAfterTact2;
    if (resultAfterF2 == EVERPARSE_STATUS_SUCCESS) {
      size_t startPosSz = (size_t)fieldStartF2;
      uint8_t *hd = (slBase + startPosSz);
      out[0] = hd;
      if (true) {
        resultAfterTact2 = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultAfterTact2 = EVERPARSE_STATUS_ERROR_ACTION_FAILED;
      }
    }
    else {
      resultAfterTact2 = resultAfterF2;
    }
    if (resultAfterTact2 == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterTact2;
    }
    else {
      (void)(errorHandlerFn("_TAct", "f2", EverParse3dErrorReasonOfResult(resultAfterTact2), EverParse3dLegacyKind(resultAfterTact2), ctxt, slBase, fieldStartTact1));
      return resultAfterTact2;
    }
  }
  else {
    return resultAfterF1;
  }
}

uint64_t GetFieldPtrValidateTact(uint8_t **out, uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = GetFieldPtrValidateTactCore(out, ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * EVERPARSE_VALIDATOR_ERROR_GENERIC) + position);
}


