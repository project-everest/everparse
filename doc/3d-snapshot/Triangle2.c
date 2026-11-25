#include "Triangle2.h"

static uint8_t Triangle2ValidateTriangleCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t Triangle2ValidateTriangleCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  /* Validating field corners */
  size_t currentPosition = slPos[0];
  uint64_t fieldStartTriangle = (uint64_t)currentPosition;
  size_t scanOffset = 0;
  size_t offsetBefore = scanOffset;
  size_t positionBefore = slPos[0];
  size_t bytesRemainingBefore = (slLen - positionBefore);
  bool hasBytesFor;
  if (offsetBefore <= bytesRemainingBefore) {
    hasBytesFor = ((size_t)12 <= (bytesRemainingBefore - offsetBefore));
  }
  else {
    hasBytesFor = false;
  }
  uint8_t res;
  if (hasBytesFor) {
    scanOffset = (offsetBefore + (size_t)12);
    res = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    res = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterTriangle;
  if (res == EVERPARSE_STATUS_SUCCESS) {
    size_t currentPosition1 = slPos[0];
    size_t newPosition = (currentPosition1 + scanOffset);
    slPos[0] = newPosition;
    resultAfterTriangle = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterTriangle = res;
  }
  if (resultAfterTriangle == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterTriangle;
  }
  else {
    (void)(errorHandlerFn("_triangle", "corners", EverParse3dErrorReasonOfResult(resultAfterTriangle), EverParse3dLegacyKind(resultAfterTriangle), ctxt, slBase, fieldStartTriangle));
    return resultAfterTriangle;
  }
}

uint64_t Triangle2ValidateTriangle(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = Triangle2ValidateTriangleCore(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * 1152921504606846976ULL) + position);
}


