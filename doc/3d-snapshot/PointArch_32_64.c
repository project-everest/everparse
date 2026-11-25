#include "PointArch_32_64.h"

static inline uint8_t PointArch3264ValidateIntCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static uint8_t PointArch3264ValidatePointCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static inline uint8_t PointArch3264ValidateIntCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  #if defined(ARCH64)
  {
    size_t scanOffset = 0;
    /* Validating field x */
    size_t currentPosition = slPos[0];
    uint64_t streamPositionAtX = (uint64_t)currentPosition;
    size_t offsetOfX = scanOffset;
    uint64_t startPositionOfX = (streamPositionAtX + (uint64_t)offsetOfX);
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    size_t offsetBeforeX = scanOffset;
    size_t positionBeforeX = slPos[0];
    size_t bytesRemainingBeforeX = (slLen - positionBeforeX);
    bool hasBytesForX;
    if (offsetBeforeX <= bytesRemainingBeforeX) {
      hasBytesForX = (8 <= (bytesRemainingBeforeX - offsetBeforeX));
    }
    else {
      hasBytesForX = false;
    }
    uint8_t resultOfX;
    if (hasBytesForX) {
      scanOffset = (offsetBeforeX + 8);
      resultOfX = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultOfX = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t res;
    if (resultOfX == EVERPARSE_STATUS_SUCCESS) {
      res = resultOfX;
    }
    else {
      (void)(errorHandlerFn("_INT", "x", EverParse3dErrorReasonOfResult(resultOfX), EverParse3dLegacyKind(resultOfX), ctxt, slBase, startPositionOfX));
      res = resultOfX;
    }
    if (res == EVERPARSE_STATUS_SUCCESS) {
      size_t currentPosition1 = slPos[0];
      size_t newPosition = (currentPosition1 + scanOffset);
      slPos[0] = newPosition;
      return EVERPARSE_STATUS_SUCCESS;
    }
    else {
      return res;
    }
  }
  #else
  {
    size_t scanOffset_1 = 0;
    /* Validating field x */
    size_t currentPosition_1 = slPos[0];
    uint64_t streamPositionAtX_1 = (uint64_t)currentPosition_1;
    size_t offsetOfX_1 = scanOffset_1;
    uint64_t startPositionOfX_1 = (streamPositionAtX_1 + (uint64_t)offsetOfX_1);
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    size_t offsetBeforeX_1 = scanOffset_1;
    size_t positionBeforeX_1 = slPos[0];
    size_t bytesRemainingBeforeX_1 = (slLen - positionBeforeX_1);
    bool hasBytesForX_1;
    if (offsetBeforeX_1 <= bytesRemainingBeforeX_1) {
      hasBytesForX_1 = (4 <= (bytesRemainingBeforeX_1 - offsetBeforeX_1));
    }
    else {
      hasBytesForX_1 = false;
    }
    uint8_t resultOfX_1;
    if (hasBytesForX_1) {
      scanOffset_1 = (offsetBeforeX_1 + 4);
      resultOfX_1 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultOfX_1 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t res_1;
    if (resultOfX_1 == EVERPARSE_STATUS_SUCCESS) {
      res_1 = resultOfX_1;
    }
    else {
      (void)(errorHandlerFn("_INT", "x", EverParse3dErrorReasonOfResult(resultOfX_1), EverParse3dLegacyKind(resultOfX_1), ctxt, slBase, startPositionOfX_1));
      res_1 = resultOfX_1;
    }
    if (res_1 == EVERPARSE_STATUS_SUCCESS) {
      size_t currentPosition1_1 = slPos[0];
      size_t newPosition_1 = (currentPosition1_1 + scanOffset_1);
      slPos[0] = newPosition_1;
      return EVERPARSE_STATUS_SUCCESS;
    }
    else {
      return res_1;
    }
  }
  #endif
}

static uint8_t PointArch3264ValidatePointCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  /* Validating field x */
  size_t currentPosition = slPos[0];
  uint64_t fieldStartPoint = (uint64_t)currentPosition;
  uint8_t resultAfterPoint = PointArch3264ValidateIntCore(ctxt, errorHandlerFn, slBase, slLen, slPos);
  uint8_t resultAfterX;
  if (resultAfterPoint == EVERPARSE_STATUS_SUCCESS) {
    resultAfterX = resultAfterPoint;
  }
  else {
    (void)(errorHandlerFn("_POINT", "x", EverParse3dErrorReasonOfResult(resultAfterPoint), EverParse3dLegacyKind(resultAfterPoint), ctxt, slBase, fieldStartPoint));
    resultAfterX = resultAfterPoint;
  }
  if (resultAfterX == EVERPARSE_STATUS_SUCCESS) {
    /* Validating field y */
    size_t currentPosition1 = slPos[0];
    uint64_t fieldStartPoint1 = (uint64_t)currentPosition1;
    uint8_t resultAfterPoint1 = PointArch3264ValidateIntCore(ctxt, errorHandlerFn, slBase, slLen, slPos);
    if (resultAfterPoint1 == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterPoint1;
    }
    else {
      (void)(errorHandlerFn("_POINT", "y", EverParse3dErrorReasonOfResult(resultAfterPoint1), EverParse3dLegacyKind(resultAfterPoint1), ctxt, slBase, fieldStartPoint1));
      return resultAfterPoint1;
    }
  }
  else {
    return resultAfterX;
  }
}

uint64_t PointArch3264ValidatePoint(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = PointArch3264ValidatePointCore(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * 1152921504606846976ULL) + position);
}


