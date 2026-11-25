#include "ColoredPoint.h"

static uint8_t ColoredPointValidateColoredPoint1Core(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static uint8_t ColoredPointValidateColoredPoint2Core(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t ColoredPointValidateColoredPoint1Core(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartColoredPoint1 = (uint64_t)currentPosition;
  size_t scanOffset = 0;
  size_t offsetBeforeColor = scanOffset;
  size_t positionBeforeColor = slPos[0];
  size_t bytesRemainingBeforeColor = (slLen - positionBeforeColor);
  bool hasBytesForColor;
  if (offsetBeforeColor <= bytesRemainingBeforeColor) {
    hasBytesForColor = ((size_t)5 <= (bytesRemainingBeforeColor - offsetBeforeColor));
  }
  else {
    hasBytesForColor = false;
  }
  uint8_t res;
  if (hasBytesForColor) {
    scanOffset = (offsetBeforeColor + (size_t)5);
    res = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    res = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterColoredPoint1;
  if (res == EVERPARSE_STATUS_SUCCESS) {
    size_t currentPosition1 = slPos[0];
    size_t newPosition = (currentPosition1 + scanOffset);
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
    (void)(errorHandlerFn("_coloredPoint1", "color", EverParse3dErrorReasonOfResult(resultAfterColoredPoint1), EverParse3dLegacyKind(resultAfterColoredPoint1), ctxt, slBase, fieldStartColoredPoint1));
    return resultAfterColoredPoint1;
  }
}

uint64_t ColoredPointValidateColoredPoint1(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = ColoredPointValidateColoredPoint1Core(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * 1152921504606846976ULL) + position);
}

static uint8_t ColoredPointValidateColoredPoint2Core(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartColoredPoint2 = (uint64_t)currentPosition;
  size_t scanOffset = 0;
  size_t offsetBeforePt = scanOffset;
  size_t positionBeforePt = slPos[0];
  size_t bytesRemainingBeforePt = (slLen - positionBeforePt);
  bool hasBytesForPt;
  if (offsetBeforePt <= bytesRemainingBeforePt) {
    hasBytesForPt = ((size_t)5 <= (bytesRemainingBeforePt - offsetBeforePt));
  }
  else {
    hasBytesForPt = false;
  }
  uint8_t res;
  if (hasBytesForPt) {
    scanOffset = (offsetBeforePt + (size_t)5);
    res = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    res = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterColoredPoint2;
  if (res == EVERPARSE_STATUS_SUCCESS) {
    size_t currentPosition1 = slPos[0];
    size_t newPosition = (currentPosition1 + scanOffset);
    slPos[0] = newPosition;
    resultAfterColoredPoint2 = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterColoredPoint2 = res;
  }
  if (resultAfterColoredPoint2 == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterColoredPoint2;
  }
  else {
    (void)(errorHandlerFn("_coloredPoint2", "pt", EverParse3dErrorReasonOfResult(resultAfterColoredPoint2), EverParse3dLegacyKind(resultAfterColoredPoint2), ctxt, slBase, fieldStartColoredPoint2));
    return resultAfterColoredPoint2;
  }
}

uint64_t ColoredPointValidateColoredPoint2(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = ColoredPointValidateColoredPoint2Core(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * 1152921504606846976ULL) + position);
}


