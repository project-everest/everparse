#include "BF.h"

static inline uint8_t BfValidateBf2bisCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static inline uint8_t BfValidateBf3Core(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static uint8_t BfValidateDummyCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static inline uint8_t BfValidateBf2bisCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t offsetInBitfield0 = 0;
  size_t currentPosition = slPos[0];
  uint64_t streamPositionAtBitfield0 = (uint64_t)currentPosition;
  size_t offsetOfBitfield0 = offsetInBitfield0;
  uint64_t startPositionOfBitfield0 = (streamPositionAtBitfield0 + (uint64_t)offsetOfBitfield0);
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  size_t offsetBeforeBitfield0 = offsetInBitfield0;
  size_t positionBeforeBitfield0 = slPos[0];
  size_t bytesRemainingBeforeBitfield0 = (slLen - positionBeforeBitfield0);
  bool hasBytesForBitfield0;
  if (offsetBeforeBitfield0 <= bytesRemainingBeforeBitfield0) {
    hasBytesForBitfield0 = (2 <= (bytesRemainingBeforeBitfield0 - offsetBeforeBitfield0));
  }
  else {
    hasBytesForBitfield0 = false;
  }
  uint8_t resultOfBitfield0;
  if (hasBytesForBitfield0) {
    offsetInBitfield0 = (offsetBeforeBitfield0 + 2);
    resultOfBitfield0 = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultOfBitfield0 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterBitfield0;
  if (resultOfBitfield0 == EVERPARSE_STATUS_SUCCESS) {
    resultAfterBitfield0 = resultOfBitfield0;
  }
  else {
    (void)(errorHandlerFn("_BF2bis", "__bitfield_0", EverParse3dErrorReasonOfResult(resultOfBitfield0), EverParse3dLegacyKind(resultOfBitfield0), ctxt, slBase, startPositionOfBitfield0));
    resultAfterBitfield0 = resultOfBitfield0;
  }
  if (resultAfterBitfield0 == EVERPARSE_STATUS_SUCCESS) {
    size_t positionOfBitfield0 = slPos[0];
    size_t positionAfterBitfield0 = (positionOfBitfield0 + 2);
    uint8_t *bytesOfBitfield0 = (slBase + positionOfBitfield0);
    slPos[0] = positionAfterBitfield0;
    uint16_t bitfield0 = EverParse3dReadUint16(bytesOfBitfield0);
    size_t currentPosition1 = slPos[0];
    uint64_t fieldStartBf2bis = (uint64_t)currentPosition1;
    size_t offsetInBitfield1 = 0;
    /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
    size_t offsetBeforeBitfield1 = offsetInBitfield1;
    size_t positionBeforeBitfield1 = slPos[0];
    size_t bytesRemainingBeforeBitfield1 = (slLen - positionBeforeBitfield1);
    bool hasBytesForBitfield1;
    if (offsetBeforeBitfield1 <= bytesRemainingBeforeBitfield1) {
      hasBytesForBitfield1 = (2 <= (bytesRemainingBeforeBitfield1 - offsetBeforeBitfield1));
    }
    else {
      hasBytesForBitfield1 = false;
    }
    uint8_t resultAfterBitfield1;
    if (hasBytesForBitfield1) {
      offsetInBitfield1 = (offsetBeforeBitfield1 + 2);
      resultAfterBitfield1 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterBitfield1 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterBf2bis;
    if (resultAfterBitfield1 == EVERPARSE_STATUS_SUCCESS) {
      size_t positionOfBitfield1 = slPos[0];
      size_t positionAfterBitfield1 = (positionOfBitfield1 + 2);
      uint8_t *bytesOfBitfield1 = (slBase + positionOfBitfield1);
      slPos[0] = positionAfterBitfield1;
      uint16_t bitfield1 = EverParse3dReadUint16(bytesOfBitfield1);
      bool bitfield1ConstraintIsOk = (EverParseGetBitfield16(bitfield1, 0, 12) < EverParseGetBitfield16(bitfield0, 0, 6));
      if (bitfield1ConstraintIsOk) {
        size_t scanOffset = 0;
        /* Validating field z */
        size_t currentPosition2 = slPos[0];
        uint64_t streamPositionAtZ = (uint64_t)currentPosition2;
        size_t offsetOfZ = scanOffset;
        uint64_t startPositionOfZ = (streamPositionAtZ + (uint64_t)offsetOfZ);
        /* Checking that we have enough space for a UINT8, i.e., 1 byte */
        size_t offsetBeforeZ = scanOffset;
        size_t positionBeforeZ = slPos[0];
        size_t bytesRemainingBeforeZ = (slLen - positionBeforeZ);
        bool hasBytesForZ;
        if (offsetBeforeZ <= bytesRemainingBeforeZ) {
          hasBytesForZ = (1 <= (bytesRemainingBeforeZ - offsetBeforeZ));
        }
        else {
          hasBytesForZ = false;
        }
        uint8_t resultOfZ;
        if (hasBytesForZ) {
          scanOffset = (offsetBeforeZ + 1);
          resultOfZ = EVERPARSE_STATUS_SUCCESS;
        }
        else {
          resultOfZ = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
        }
        uint8_t res;
        if (resultOfZ == EVERPARSE_STATUS_SUCCESS) {
          res = resultOfZ;
        }
        else {
          (void)(errorHandlerFn("_BF2bis", "z", EverParse3dErrorReasonOfResult(resultOfZ), EverParse3dLegacyKind(resultOfZ), ctxt, slBase, startPositionOfZ));
          res = resultOfZ;
        }
        if (res == EVERPARSE_STATUS_SUCCESS) {
          size_t currentPosition3 = slPos[0];
          size_t newPosition = (currentPosition3 + scanOffset);
          slPos[0] = newPosition;
          resultAfterBf2bis = EVERPARSE_STATUS_SUCCESS;
        }
        else {
          resultAfterBf2bis = res;
        }
      }
      else {
        resultAfterBf2bis = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
      }
    }
    else {
      resultAfterBf2bis = resultAfterBitfield1;
    }
    if (resultAfterBf2bis == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterBf2bis;
    }
    else {
      (void)(errorHandlerFn("_BF2bis", "__bitfield_1", EverParse3dErrorReasonOfResult(resultAfterBf2bis), EverParse3dLegacyKind(resultAfterBf2bis), ctxt, slBase, fieldStartBf2bis));
      return resultAfterBf2bis;
    }
  }
  else {
    return resultAfterBitfield0;
  }
}

static inline uint8_t BfValidateBf3Core(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t offsetInBitfield0 = 0;
  size_t currentPosition = slPos[0];
  uint64_t streamPositionAtBitfield0 = (uint64_t)currentPosition;
  size_t offsetOfBitfield0 = offsetInBitfield0;
  uint64_t startPositionOfBitfield0 = (streamPositionAtBitfield0 + (uint64_t)offsetOfBitfield0);
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  size_t offsetBeforeBitfield0 = offsetInBitfield0;
  size_t positionBeforeBitfield0 = slPos[0];
  size_t bytesRemainingBeforeBitfield0 = (slLen - positionBeforeBitfield0);
  bool hasBytesForBitfield0;
  if (offsetBeforeBitfield0 <= bytesRemainingBeforeBitfield0) {
    hasBytesForBitfield0 = (2 <= (bytesRemainingBeforeBitfield0 - offsetBeforeBitfield0));
  }
  else {
    hasBytesForBitfield0 = false;
  }
  uint8_t resultOfBitfield0;
  if (hasBytesForBitfield0) {
    offsetInBitfield0 = (offsetBeforeBitfield0 + 2);
    resultOfBitfield0 = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultOfBitfield0 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterBitfield0;
  if (resultOfBitfield0 == EVERPARSE_STATUS_SUCCESS) {
    resultAfterBitfield0 = resultOfBitfield0;
  }
  else {
    (void)(errorHandlerFn("_BF3", "__bitfield_0", EverParse3dErrorReasonOfResult(resultOfBitfield0), EverParse3dLegacyKind(resultOfBitfield0), ctxt, slBase, startPositionOfBitfield0));
    resultAfterBitfield0 = resultOfBitfield0;
  }
  if (resultAfterBitfield0 == EVERPARSE_STATUS_SUCCESS) {
    size_t positionOfBitfield0 = slPos[0];
    size_t positionAfterBitfield0 = (positionOfBitfield0 + 2);
    uint8_t *bytesOfBitfield0 = (slBase + positionOfBitfield0);
    slPos[0] = positionAfterBitfield0;
    uint16_t bitfield0 = EverParse3dReadUint16Be(bytesOfBitfield0);
    size_t currentPosition1 = slPos[0];
    uint64_t fieldStartBf3 = (uint64_t)currentPosition1;
    size_t offsetInBitfield1 = 0;
    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
    size_t offsetBeforeBitfield1 = offsetInBitfield1;
    size_t positionBeforeBitfield1 = slPos[0];
    size_t bytesRemainingBeforeBitfield1 = (slLen - positionBeforeBitfield1);
    bool hasBytesForBitfield1;
    if (offsetBeforeBitfield1 <= bytesRemainingBeforeBitfield1) {
      hasBytesForBitfield1 = (2 <= (bytesRemainingBeforeBitfield1 - offsetBeforeBitfield1));
    }
    else {
      hasBytesForBitfield1 = false;
    }
    uint8_t resultAfterBitfield1;
    if (hasBytesForBitfield1) {
      offsetInBitfield1 = (offsetBeforeBitfield1 + 2);
      resultAfterBitfield1 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterBitfield1 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterBf3;
    if (resultAfterBitfield1 == EVERPARSE_STATUS_SUCCESS) {
      size_t positionOfBitfield1 = slPos[0];
      size_t positionAfterBitfield1 = (positionOfBitfield1 + 2);
      uint8_t *bytesOfBitfield1 = (slBase + positionOfBitfield1);
      slPos[0] = positionAfterBitfield1;
      uint16_t bitfield1 = EverParse3dReadUint16Be(bytesOfBitfield1);
      bool bitfield1ConstraintIsOk = (EverParseGetBitfield16MsbFirst(bitfield1, 0, 12) < EverParseGetBitfield16MsbFirst(bitfield0, 0, 6));
      if (bitfield1ConstraintIsOk) {
        size_t scanOffset = 0;
        /* Validating field z */
        size_t currentPosition2 = slPos[0];
        uint64_t streamPositionAtZ = (uint64_t)currentPosition2;
        size_t offsetOfZ = scanOffset;
        uint64_t startPositionOfZ = (streamPositionAtZ + (uint64_t)offsetOfZ);
        /* Checking that we have enough space for a UINT8BE, i.e., 1 byte */
        size_t offsetBeforeZ = scanOffset;
        size_t positionBeforeZ = slPos[0];
        size_t bytesRemainingBeforeZ = (slLen - positionBeforeZ);
        bool hasBytesForZ;
        if (offsetBeforeZ <= bytesRemainingBeforeZ) {
          hasBytesForZ = (1 <= (bytesRemainingBeforeZ - offsetBeforeZ));
        }
        else {
          hasBytesForZ = false;
        }
        uint8_t resultOfZ;
        if (hasBytesForZ) {
          scanOffset = (offsetBeforeZ + 1);
          resultOfZ = EVERPARSE_STATUS_SUCCESS;
        }
        else {
          resultOfZ = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
        }
        uint8_t res;
        if (resultOfZ == EVERPARSE_STATUS_SUCCESS) {
          res = resultOfZ;
        }
        else {
          (void)(errorHandlerFn("_BF3", "z", EverParse3dErrorReasonOfResult(resultOfZ), EverParse3dLegacyKind(resultOfZ), ctxt, slBase, startPositionOfZ));
          res = resultOfZ;
        }
        if (res == EVERPARSE_STATUS_SUCCESS) {
          size_t currentPosition3 = slPos[0];
          size_t newPosition = (currentPosition3 + scanOffset);
          slPos[0] = newPosition;
          resultAfterBf3 = EVERPARSE_STATUS_SUCCESS;
        }
        else {
          resultAfterBf3 = res;
        }
      }
      else {
        resultAfterBf3 = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
      }
    }
    else {
      resultAfterBf3 = resultAfterBitfield1;
    }
    if (resultAfterBf3 == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterBf3;
    }
    else {
      (void)(errorHandlerFn("_BF3", "__bitfield_1", EverParse3dErrorReasonOfResult(resultAfterBf3), EverParse3dLegacyKind(resultAfterBf3), ctxt, slBase, fieldStartBf3));
      return resultAfterBf3;
    }
  }
  else {
    return resultAfterBitfield0;
  }
}

static uint8_t BfValidateDummyCore(EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  /* Validating field emp2 */
  size_t currentPosition = slPos[0];
  uint64_t fieldStartDummy = (uint64_t)currentPosition;
  uint8_t resultAfterDummy = BfValidateBf2bisCore(ctxt, errorHandlerFn, slBase, slLen, slPos);
  uint8_t resultAfterEmp2;
  if (resultAfterDummy == EVERPARSE_STATUS_SUCCESS) {
    resultAfterEmp2 = resultAfterDummy;
  }
  else {
    (void)(errorHandlerFn("_dummy", "emp2", EverParse3dErrorReasonOfResult(resultAfterDummy), EverParse3dLegacyKind(resultAfterDummy), ctxt, slBase, fieldStartDummy));
    resultAfterEmp2 = resultAfterDummy;
  }
  if (resultAfterEmp2 == EVERPARSE_STATUS_SUCCESS) {
    /* Validating field emp3 */
    size_t currentPosition1 = slPos[0];
    uint64_t fieldStartDummy1 = (uint64_t)currentPosition1;
    uint8_t resultAfterDummy1 = BfValidateBf3Core(ctxt, errorHandlerFn, slBase, slLen, slPos);
    if (resultAfterDummy1 == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterDummy1;
    }
    else {
      (void)(errorHandlerFn("_dummy", "emp3", EverParse3dErrorReasonOfResult(resultAfterDummy1), EverParse3dLegacyKind(resultAfterDummy1), ctxt, slBase, fieldStartDummy1));
      return resultAfterDummy1;
    }
  }
  else {
    return resultAfterEmp2;
  }
}

uint64_t BfValidateDummy(uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = BfValidateDummyCore(ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * 1152921504606846976ULL) + position);
}


