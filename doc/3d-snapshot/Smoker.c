#include "Smoker.h"

static uint8_t SmokerValidateSmokerCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t SmokerValidateSmokerCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartSmoker = (uint64_t)currentPosition;
  size_t offsetInAge = 0;
  /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
  size_t offsetBeforeAge = offsetInAge;
  size_t positionBeforeAge = slPos[0];
  size_t bytesRemainingBeforeAge = (slLen - positionBeforeAge);
  bool hasBytesForAge;
  if (offsetBeforeAge <= bytesRemainingBeforeAge) {
    hasBytesForAge = (4 <= (bytesRemainingBeforeAge - offsetBeforeAge));
  }
  else {
    hasBytesForAge = false;
  }
  uint8_t resultAfterAge;
  if (hasBytesForAge) {
    offsetInAge = (offsetBeforeAge + 4);
    resultAfterAge = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultAfterAge = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterSmoker;
  if (resultAfterAge == EVERPARSE_STATUS_SUCCESS) {
    size_t positionOfAge = slPos[0];
    size_t positionAfterAge = (positionOfAge + 4);
    uint8_t *bytesOfAge = (slBase + positionOfAge);
    slPos[0] = positionAfterAge;
    uint32_t age = EverParse3dReadUint32(bytesOfAge);
    bool ageConstraintIsOk = (age >= (uint32_t)21);
    if (ageConstraintIsOk) {
      size_t scanOffset = 0;
      /* Validating field cigarettesConsumed */
      size_t currentPosition1 = slPos[0];
      uint64_t streamPositionAtCigarettesConsumed = (uint64_t)currentPosition1;
      size_t offsetOfCigarettesConsumed = scanOffset;
      uint64_t startPositionOfCigarettesConsumed = (streamPositionAtCigarettesConsumed + (uint64_t)offsetOfCigarettesConsumed);
      /* Checking that we have enough space for a UINT8, i.e., 1 byte */
      size_t offsetBeforeCigarettesConsumed = scanOffset;
      size_t positionBeforeCigarettesConsumed = slPos[0];
      size_t bytesRemainingBeforeCigarettesConsumed = (slLen - positionBeforeCigarettesConsumed);
      bool hasBytesForCigarettesConsumed;
      if (offsetBeforeCigarettesConsumed <= bytesRemainingBeforeCigarettesConsumed) {
        hasBytesForCigarettesConsumed = (1 <= (bytesRemainingBeforeCigarettesConsumed - offsetBeforeCigarettesConsumed));
      }
      else {
        hasBytesForCigarettesConsumed = false;
      }
      uint8_t resultOfCigarettesConsumed;
      if (hasBytesForCigarettesConsumed) {
        scanOffset = (offsetBeforeCigarettesConsumed + 1);
        resultOfCigarettesConsumed = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultOfCigarettesConsumed = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
      }
      uint8_t res;
      if (resultOfCigarettesConsumed == EVERPARSE_STATUS_SUCCESS) {
        res = resultOfCigarettesConsumed;
      }
      else {
        (void)(errorHandlerFn("_smoker", "cigarettesConsumed", EverParse3dErrorReasonOfResult(resultOfCigarettesConsumed), EverParse3dLegacyKind(resultOfCigarettesConsumed), ctxt, slBase, startPositionOfCigarettesConsumed));
        res = resultOfCigarettesConsumed;
      }
      if (res == EVERPARSE_STATUS_SUCCESS) {
        size_t currentPosition2 = slPos[0];
        size_t newPosition = (currentPosition2 + scanOffset);
        slPos[0] = newPosition;
        resultAfterSmoker = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultAfterSmoker = res;
      }
    }
    else {
      resultAfterSmoker = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
    }
  }
  else {
    resultAfterSmoker = resultAfterAge;
  }
  if (resultAfterSmoker == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterSmoker;
  }
  else {
    (void)(errorHandlerFn("_smoker", "age", EverParse3dErrorReasonOfResult(resultAfterSmoker), EverParse3dLegacyKind(resultAfterSmoker), ctxt, slBase, fieldStartSmoker));
    return resultAfterSmoker;
  }
}

uint64_t SmokerValidateSmoker(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = SmokerValidateSmokerCore(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * EVERPARSE_VALIDATOR_ERROR_GENERIC) + position);
}


