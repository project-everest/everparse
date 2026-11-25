#include "Base.h"

static uint8_t BaseValidateUlongCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos, size_t *pos);
static uint8_t BaseValidatePairCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t BaseValidateUlongCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos, size_t *pos) {
  size_t currentPosition = slPos[0];
  uint64_t streamPositionAtMissing = (uint64_t)currentPosition;
  size_t offsetOfMissing = pos[0];
  uint64_t startPositionOfMissing = (streamPositionAtMissing + (uint64_t)offsetOfMissing);
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t offsetBeforeMissing = pos[0];
  size_t positionBeforeMissing = slPos[0];
  size_t bytesRemainingBeforeMissing = (slLen - positionBeforeMissing);
  bool hasBytesForMissing;
  if (offsetBeforeMissing <= bytesRemainingBeforeMissing) {
    hasBytesForMissing = (4 <= (bytesRemainingBeforeMissing - offsetBeforeMissing));
  }
  else {
    hasBytesForMissing = false;
  }
  uint8_t resultOfMissing;
  if (hasBytesForMissing) {
    pos[0] = (offsetBeforeMissing + 4);
    resultOfMissing = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultOfMissing = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  if (resultOfMissing == EVERPARSE_STATUS_SUCCESS) {
    return resultOfMissing;
  }
  else {
    (void)(errorHandlerFn("___ULONG", "missing", EverParse3dErrorReasonOfResult(resultOfMissing), EverParse3dLegacyKind(resultOfMissing), ctxt, slBase, startPositionOfMissing));
    return resultOfMissing;
  }
}

uint64_t BaseValidateUlong(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  size_t lookahead = 0;
  uint8_t status = BaseValidateUlongCore(ctxt, handler, input, len, &cursor, &lookahead);
  uint64_t position;
  if (status == EVERPARSE_STATUS_SUCCESS) {
    position = (start + (uint64_t)lookahead);
  }
  else {
    position = start;
  }
  return ((EverParse3dLegacyKind(status) * 1152921504606846976ULL) + position);
}

static uint8_t BaseValidatePairCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartPair = (uint64_t)currentPosition;
  size_t scanOffset = 0;
  size_t offsetBeforeFirst = scanOffset;
  size_t positionBeforeFirst = slPos[0];
  size_t bytesRemainingBeforeFirst = (slLen - positionBeforeFirst);
  bool hasBytesForFirst;
  if (offsetBeforeFirst <= bytesRemainingBeforeFirst) {
    hasBytesForFirst = ((size_t)8 <= (bytesRemainingBeforeFirst - offsetBeforeFirst));
  }
  else {
    hasBytesForFirst = false;
  }
  uint8_t res;
  if (hasBytesForFirst) {
    scanOffset = (offsetBeforeFirst + (size_t)8);
    res = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    res = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterPair;
  if (res == EVERPARSE_STATUS_SUCCESS) {
    size_t currentPosition1 = slPos[0];
    size_t newPosition = (currentPosition1 + scanOffset);
    slPos[0] = newPosition;
    resultAfterPair = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterPair = res;
  }
  if (resultAfterPair == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterPair;
  }
  else {
    (void)(errorHandlerFn("_Pair", "first", EverParse3dErrorReasonOfResult(resultAfterPair), EverParse3dLegacyKind(resultAfterPair), ctxt, slBase, fieldStartPair));
    return resultAfterPair;
  }
}

uint64_t BaseValidatePair(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = BaseValidatePairCore(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * 1152921504606846976ULL) + position);
}


