#include "Align.h"

static uint8_t AlignValidateColoredPoint1Core(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t AlignValidateColoredPoint1Core(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartColoredPoint1 = (uint64_t)currentPosition;
  size_t scanOffset = 0;
  size_t offsetBeforeColor = scanOffset;
  size_t positionBeforeColor = slPos[0];
  size_t bytesRemainingBeforeColor = (slLen - positionBeforeColor);
  bool hasBytesForColor;
  if (offsetBeforeColor <= bytesRemainingBeforeColor) {
    hasBytesForColor = ((size_t)6 <= (bytesRemainingBeforeColor - offsetBeforeColor));
  }
  else {
    hasBytesForColor = false;
  }
  uint8_t res;
  if (hasBytesForColor) {
    scanOffset = (offsetBeforeColor + (size_t)6);
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

uint64_t AlignValidateColoredPoint1(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = AlignValidateColoredPoint1Core(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * EVERPARSE_VALIDATOR_ERROR_GENERIC) + position);
}


