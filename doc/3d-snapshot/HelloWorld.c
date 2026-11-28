#include "HelloWorld.h"

static uint8_t HelloWorldValidatePointCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t HelloWorldValidatePointCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartPoint = (uint64_t)currentPosition;
  size_t scanOffset = 0;
  size_t offsetBeforeX = scanOffset;
  size_t positionBeforeX = slPos[0];
  size_t bytesRemainingBeforeX = (slLen - positionBeforeX);
  bool hasBytesForX;
  if (offsetBeforeX <= bytesRemainingBeforeX) {
    hasBytesForX = ((size_t)4 <= (bytesRemainingBeforeX - offsetBeforeX));
  }
  else {
    hasBytesForX = false;
  }
  uint8_t res;
  if (hasBytesForX) {
    scanOffset = (offsetBeforeX + (size_t)4);
    res = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    res = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterPoint;
  if (res == EVERPARSE_STATUS_SUCCESS) {
    size_t currentPosition1 = slPos[0];
    size_t newPosition = (currentPosition1 + scanOffset);
    slPos[0] = newPosition;
    resultAfterPoint = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterPoint = res;
  }
  if (resultAfterPoint == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterPoint;
  }
  else {
    (void)(errorHandlerFn("_point", "x", EverParse3dErrorReasonOfResult(resultAfterPoint), EverParse3dLegacyKind(resultAfterPoint), ctxt, slBase, fieldStartPoint));
    return resultAfterPoint;
  }
}

uint64_t HelloWorldValidatePoint(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = HelloWorldValidatePointCore(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * EVERPARSE_VALIDATOR_ERROR_GENERIC) + position);
}


