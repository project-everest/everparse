#include "SpecializeDep1.h"

static void SpecializeDep1CopyBytes(uint64_t numbytes, const char * tn, const char * fieldName, const char * fd, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER err, uint64_t *readOffset, uint64_t *writeOffset, BOOLEAN *failed, uint64_t src, uint64_t sz, EVERPARSE_COPY_BUFFER_T dest);
static void SpecializeDep1Specialized32ProbeUnion(uint8_t tag, const char * tn, const char * fieldName, const char * fd, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER err, uint64_t *readOffset, uint64_t *writeOffset, BOOLEAN *failed, uint64_t src, uint64_t sz, EVERPARSE_COPY_BUFFER_T dest);
static void SpecializeDep1Specialized32ProbeTlv(uint16_t ___Len, const char * tn, const char * fieldName, const char * fd, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER err, uint64_t *readOffset, uint64_t *writeOffset, BOOLEAN *failed, uint64_t src, uint64_t sz, EVERPARSE_COPY_BUFFER_T dest);
static inline uint8_t SpecializeDep1ValidateUnionCore(uint8_t tag, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static inline uint8_t SpecializeDep1ValidateTlvCore(uint16_t ___Len, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static inline uint8_t SpecializeDep1ValidateSpecializedWrapper32Core(uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static inline uint8_t SpecializeDep1ValidateWrapperCore(void (*___probe_tlv)(uint16_t, const char *, const char *, const char *, EVERPARSE_APP_CTXT, void (*)(const char *, const char *, const char *, uint64_t, uint8_t *, uint8_t *, uint64_t), uint64_t *, uint64_t *, BOOLEAN *, uint64_t, uint64_t, EVERPARSE_COPY_BUFFER_T), uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);
static void SpecializeDep1EntryProbeWrapper0Tlv(uint16_t ____arg0, const char * tn, const char * fieldName, const char * fd, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER err, uint64_t *readOffset, uint64_t *writeOffset, BOOLEAN *failed, uint64_t src, uint64_t sz, EVERPARSE_COPY_BUFFER_T dest);
static uint8_t SpecializeDep1ValidateEntryCore(bool ___Requestor32, uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static void SpecializeDep1CopyBytes(uint64_t numbytes, const char * tn, const char * fieldName, const char * fd, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER err, uint64_t *readOffset, uint64_t *writeOffset, BOOLEAN *failed, uint64_t src, uint64_t sz, EVERPARSE_COPY_BUFFER_T dest) {
  (void)tn;
  (void)fieldName;
  (void)fd;
  (void)ctxt;
  (void)err;
  (void)sz;
  uint64_t rd = readOffset[0];
  uint64_t wr = writeOffset[0];
  BOOLEAN ok = (ProbeAndCopy(numbytes, rd, wr, src, dest));
  if (ok != 0) {
    readOffset[0] = (rd + numbytes);
    writeOffset[0] = (wr + numbytes);
  }
  else {
    failed[0] = 1;
  }
}

static void SpecializeDep1Specialized32ProbeUnion(uint8_t tag, const char * tn, const char * fieldName, const char * fd, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER err, uint64_t *readOffset, uint64_t *writeOffset, BOOLEAN *failed, uint64_t src, uint64_t sz, EVERPARSE_COPY_BUFFER_T dest) {
  if (tag == 0) {
    SpecializeDep1CopyBytes(1, tn, fieldName, fd, ctxt, err, readOffset, writeOffset, failed, src, sz, dest);
    BOOLEAN hasFailed = failed[0];
    if (hasFailed != 0) {
      (void)(err(tn, fieldName, "case0", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
    }
  }
  else {
    if (tag == 1) {
      SpecializeDep1CopyBytes(2, tn, fieldName, fd, ctxt, err, readOffset, writeOffset, failed, src, sz, dest);
      BOOLEAN hasFailed_1 = failed[0];
      if (hasFailed_1 != 0) {
        (void)(err(tn, fieldName, "case1", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
      }
    }
    else {
      SpecializeDep1CopyBytes(4, tn, fieldName, fd, ctxt, err, readOffset, writeOffset, failed, src, sz, dest);
      BOOLEAN hasFailed_2 = failed[0];
      if (hasFailed_2 != 0) {
        (void)(err(tn, fieldName, "other", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
      }
    }
  }
  BOOLEAN hasFailed_3 = failed[0];
  if (hasFailed_3 != 0) {
    (void)(err(tn, fieldName, "field", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
  }
}

static void SpecializeDep1Specialized32ProbeTlv(uint16_t ___Len, const char * tn, const char * fieldName, const char * fd, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER err, uint64_t *readOffset, uint64_t *writeOffset, BOOLEAN *failed, uint64_t src, uint64_t sz, EVERPARSE_COPY_BUFFER_T dest) {
  uint64_t rd = readOffset[0];
  uint8_t v = (ProbeAndReadU8(failed, rd, src, dest));
  BOOLEAN hasFailed = failed[0];
  uint8_t res1;
  if (hasFailed != 0) {
    (void)(err(tn, fieldName, fd, 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
    res1 = v;
  }
  else {
    readOffset[0] = (rd + 1);
    res1 = v;
  }
  BOOLEAN hasFailed1 = failed[0];
  if (hasFailed1 != 0) {
    (void)(err(tn, fieldName, "tag", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
  }
  else {
    uint64_t wr = writeOffset[0];
    BOOLEAN ok = (WriteU8(res1, wr, dest));
    if (ok != 0) {
      writeOffset[0] = (wr + 1);
    }
    else {
      failed[0] = 1;
    }
    BOOLEAN hasFailed2 = failed[0];
    if (hasFailed2 != 0) {
      (void)(err(tn, fieldName, "tag", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
    }
    else {
      SpecializeDep1CopyBytes(4, tn, fieldName, fd, ctxt, err, readOffset, writeOffset, failed, src, sz, dest);
      BOOLEAN hasFailed3 = failed[0];
      if (hasFailed3 != 0) {
        (void)(err(tn, fieldName, "length", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
      }
      else {
        uint64_t ctr = (uint64_t)(uint32_t)___Len;
        bool stop = false;
        while (!(stop)) {
          uint64_t c0 = ctr;
          BOOLEAN hf0 = failed[0];
          if (hf0 != 0) {
            stop = true;
          }
          else {
            if (c0 == 0) {
              stop = true;
            }
            else {
              uint64_t r0 = readOffset[0];
              SpecializeDep1Specialized32ProbeUnion(res1, tn, fieldName, fd, ctxt, err, readOffset, writeOffset, failed, src, sz, dest);
              BOOLEAN hasFailed4 = failed[0];
              if (hasFailed4 != 0) {
                (void)(err(tn, fieldName, "payload", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
              }
              BOOLEAN hf1 = failed[0];
              uint64_t r1 = readOffset[0];
              if (hf1 != 0) {
                (void)(err(tn, fieldName, fd, 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
                stop = true;
              }
              else {
                if (r1 == r0) {
                  (void)(err(tn, fieldName, fd, 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
                  failed[0] = 1;
                  stop = true;
                }
                else {
                  uint64_t bytesRead = (r1 - r0);
                  if (c0 < bytesRead) {
                    (void)(err(tn, fieldName, fd, 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
                    failed[0] = 1;
                    stop = true;
                  }
                  else {
                    ctr = (c0 - bytesRead);
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

static inline uint8_t SpecializeDep1ValidateUnionCore(uint8_t tag, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  if (tag == 0) {
    size_t scanOffset = 0;
    /* Validating field case0 */
    size_t currentPosition = slPos[0];
    uint64_t streamPositionAtCase0 = (uint64_t)currentPosition;
    size_t offsetOfCase0 = scanOffset;
    uint64_t startPositionOfCase0 = (streamPositionAtCase0 + (uint64_t)offsetOfCase0);
    /* Checking that we have enough space for a UINT8, i.e., 1 byte */
    size_t offsetBeforeCase0 = scanOffset;
    size_t positionBeforeCase0 = slPos[0];
    size_t bytesRemainingBeforeCase0 = (slLen - positionBeforeCase0);
    bool hasBytesForCase0;
    if (offsetBeforeCase0 <= bytesRemainingBeforeCase0) {
      hasBytesForCase0 = (1 <= (bytesRemainingBeforeCase0 - offsetBeforeCase0));
    }
    else {
      hasBytesForCase0 = false;
    }
    uint8_t resultOfCase0;
    if (hasBytesForCase0) {
      scanOffset = (offsetBeforeCase0 + 1);
      resultOfCase0 = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultOfCase0 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t res;
    if (resultOfCase0 == EVERPARSE_STATUS_SUCCESS) {
      res = resultOfCase0;
    }
    else {
      (void)(errorHandlerFn("_UNION", "case0", EverParse3dErrorReasonOfResult(resultOfCase0), EverParse3dLegacyKind(resultOfCase0), ctxt, slBase, startPositionOfCase0));
      res = resultOfCase0;
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
  else {
    if (tag == 1) {
      size_t scanOffset_1 = 0;
      /* Validating field case1 */
      size_t currentPosition_1 = slPos[0];
      uint64_t streamPositionAtCase1 = (uint64_t)currentPosition_1;
      size_t offsetOfCase1 = scanOffset_1;
      uint64_t startPositionOfCase1 = (streamPositionAtCase1 + (uint64_t)offsetOfCase1);
      /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
      size_t offsetBeforeCase1 = scanOffset_1;
      size_t positionBeforeCase1 = slPos[0];
      size_t bytesRemainingBeforeCase1 = (slLen - positionBeforeCase1);
      bool hasBytesForCase1;
      if (offsetBeforeCase1 <= bytesRemainingBeforeCase1) {
        hasBytesForCase1 = (2 <= (bytesRemainingBeforeCase1 - offsetBeforeCase1));
      }
      else {
        hasBytesForCase1 = false;
      }
      uint8_t resultOfCase1;
      if (hasBytesForCase1) {
        scanOffset_1 = (offsetBeforeCase1 + 2);
        resultOfCase1 = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultOfCase1 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
      }
      uint8_t res_1;
      if (resultOfCase1 == EVERPARSE_STATUS_SUCCESS) {
        res_1 = resultOfCase1;
      }
      else {
        (void)(errorHandlerFn("_UNION", "case1", EverParse3dErrorReasonOfResult(resultOfCase1), EverParse3dLegacyKind(resultOfCase1), ctxt, slBase, startPositionOfCase1));
        res_1 = resultOfCase1;
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
    else {
      size_t scanOffset_2 = 0;
      /* Validating field other */
      size_t currentPosition_2 = slPos[0];
      uint64_t streamPositionAtOther = (uint64_t)currentPosition_2;
      size_t offsetOfOther = scanOffset_2;
      uint64_t startPositionOfOther = (streamPositionAtOther + (uint64_t)offsetOfOther);
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      size_t offsetBeforeOther = scanOffset_2;
      size_t positionBeforeOther = slPos[0];
      size_t bytesRemainingBeforeOther = (slLen - positionBeforeOther);
      bool hasBytesForOther;
      if (offsetBeforeOther <= bytesRemainingBeforeOther) {
        hasBytesForOther = (4 <= (bytesRemainingBeforeOther - offsetBeforeOther));
      }
      else {
        hasBytesForOther = false;
      }
      uint8_t resultOfOther;
      if (hasBytesForOther) {
        scanOffset_2 = (offsetBeforeOther + 4);
        resultOfOther = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultOfOther = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
      }
      uint8_t res_2;
      if (resultOfOther == EVERPARSE_STATUS_SUCCESS) {
        res_2 = resultOfOther;
      }
      else {
        (void)(errorHandlerFn("_UNION", "other", EverParse3dErrorReasonOfResult(resultOfOther), EverParse3dLegacyKind(resultOfOther), ctxt, slBase, startPositionOfOther));
        res_2 = resultOfOther;
      }
      if (res_2 == EVERPARSE_STATUS_SUCCESS) {
        size_t currentPosition1_2 = slPos[0];
        size_t newPosition_2 = (currentPosition1_2 + scanOffset_2);
        slPos[0] = newPosition_2;
        return EVERPARSE_STATUS_SUCCESS;
      }
      else {
        return res_2;
      }
    }
  }
}

static inline uint8_t SpecializeDep1ValidateTlvCore(uint16_t ___Len, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t offsetInTag = 0;
  size_t currentPosition = slPos[0];
  uint64_t streamPositionAtTag = (uint64_t)currentPosition;
  size_t offsetOfTag = offsetInTag;
  uint64_t startPositionOfTag = (streamPositionAtTag + (uint64_t)offsetOfTag);
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  size_t offsetBeforeTag = offsetInTag;
  size_t positionBeforeTag = slPos[0];
  size_t bytesRemainingBeforeTag = (slLen - positionBeforeTag);
  bool hasBytesForTag;
  if (offsetBeforeTag <= bytesRemainingBeforeTag) {
    hasBytesForTag = (1 <= (bytesRemainingBeforeTag - offsetBeforeTag));
  }
  else {
    hasBytesForTag = false;
  }
  uint8_t resultOfTag;
  if (hasBytesForTag) {
    offsetInTag = (offsetBeforeTag + 1);
    resultOfTag = EVERPARSE_STATUS_SUCCESS;
  }
  else {
    resultOfTag = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
  }
  uint8_t resultAfterTag;
  if (resultOfTag == EVERPARSE_STATUS_SUCCESS) {
    resultAfterTag = resultOfTag;
  }
  else {
    (void)(errorHandlerFn("_TLV", "tag", EverParse3dErrorReasonOfResult(resultOfTag), EverParse3dLegacyKind(resultOfTag), ctxt, slBase, startPositionOfTag));
    resultAfterTag = resultOfTag;
  }
  if (resultAfterTag == EVERPARSE_STATUS_SUCCESS) {
    size_t positionOfTag = slPos[0];
    size_t positionAfterTag = (positionOfTag + 1);
    uint8_t *bytesOfTag = (slBase + positionOfTag);
    slPos[0] = positionAfterTag;
    uint8_t tag = EverParse3dReadUint8(bytesOfTag);
    size_t currentPosition1 = slPos[0];
    uint64_t fieldStartTlv = (uint64_t)currentPosition1;
    size_t offsetInLength = 0;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    size_t offsetBeforeLength = offsetInLength;
    size_t positionBeforeLength = slPos[0];
    size_t bytesRemainingBeforeLength = (slLen - positionBeforeLength);
    bool hasBytesForLength;
    if (offsetBeforeLength <= bytesRemainingBeforeLength) {
      hasBytesForLength = (4 <= (bytesRemainingBeforeLength - offsetBeforeLength));
    }
    else {
      hasBytesForLength = false;
    }
    uint8_t resultAfterLength;
    if (hasBytesForLength) {
      offsetInLength = (offsetBeforeLength + 4);
      resultAfterLength = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterLength = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterTlv;
    if (resultAfterLength == EVERPARSE_STATUS_SUCCESS) {
      size_t positionOfLength = slPos[0];
      size_t positionAfterLength = (positionOfLength + 4);
      uint8_t *bytesOfLength = (slBase + positionOfLength);
      slPos[0] = positionAfterLength;
      uint32_t length = EverParse3dReadUint32(bytesOfLength);
      bool lengthConstraintIsOk = (length == (uint32_t)___Len);
      if (lengthConstraintIsOk) {
        /* Validating field payload */
        size_t currentPosition2 = slPos[0];
        uint64_t fieldStartTlv1 = (uint64_t)currentPosition2;
        size_t nSz = (size_t)(uint32_t)___Len;
        size_t positionBefore = slPos[0];
        size_t bytesRemainingBefore = (slLen - positionBefore);
        bool hasBytes = (nSz <= bytesRemainingBefore);
        uint8_t resultAfterTlv_1;
        if (!(hasBytes)) {
          resultAfterTlv_1 = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
        }
        else {
          size_t currentPosition3 = slPos[0];
          size_t tr = (currentPosition3 + nSz);
          uint8_t res = EVERPARSE_STATUS_SUCCESS;
          bool stop = false;
          while (!(stop)) {
            size_t positionBeforeListElement = slPos[0];
            size_t bytesRemainingBeforeListElement = (tr - positionBeforeListElement);
            bool hasMore = (1 <= bytesRemainingBeforeListElement);
            if (!(hasMore)) {
              stop = true;
            }
            else {
              size_t currentPosition4 = slPos[0];
              uint64_t fieldStartTlv2 = (uint64_t)currentPosition4;
              uint8_t resultAfterTlv_2 = SpecializeDep1ValidateUnionCore(tag, ctxt, errorHandlerFn, slBase, tr, slPos);
              uint8_t r;
              if (resultAfterTlv_2 == EVERPARSE_STATUS_SUCCESS) {
                r = resultAfterTlv_2;
              }
              else {
                (void)(errorHandlerFn("_TLV", "payload.element", EverParse3dErrorReasonOfResult(resultAfterTlv_2), EverParse3dLegacyKind(resultAfterTlv_2), ctxt, slBase, fieldStartTlv2));
                r = resultAfterTlv_2;
              }
              if (!(r == EVERPARSE_STATUS_SUCCESS)) {
                res = r;
                stop = true;
              }
            }
          }
          if (res == EVERPARSE_STATUS_SUCCESS) {
            resultAfterTlv_1 = res;
          }
          else {
            resultAfterTlv_1 = res;
          }
        }
        if (resultAfterTlv_1 == EVERPARSE_STATUS_SUCCESS) {
          resultAfterTlv = resultAfterTlv_1;
        }
        else {
          (void)(errorHandlerFn("_TLV", "payload", EverParse3dErrorReasonOfResult(resultAfterTlv_1), EverParse3dLegacyKind(resultAfterTlv_1), ctxt, slBase, fieldStartTlv1));
          resultAfterTlv = resultAfterTlv_1;
        }
      }
      else {
        resultAfterTlv = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
      }
    }
    else {
      resultAfterTlv = resultAfterLength;
    }
    if (resultAfterTlv == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterTlv;
    }
    else {
      (void)(errorHandlerFn("_TLV", "length", EverParse3dErrorReasonOfResult(resultAfterTlv), EverParse3dLegacyKind(resultAfterTlv), ctxt, slBase, fieldStartTlv));
      return resultAfterTlv;
    }
  }
  else {
    return resultAfterTag;
  }
}

static inline uint8_t SpecializeDep1ValidateSpecializedWrapper32Core(uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartSpecializedWrapper32 = (uint64_t)currentPosition;
  /* Validating field __precondition */
  bool preconditionConstraintIsOk = (___Len > (uint16_t)5);
  uint8_t resultAfterSpecializedWrapper32;
  if (preconditionConstraintIsOk) {
    size_t currentPosition1 = slPos[0];
    uint64_t fieldStartSpecializedWrapper321 = (uint64_t)currentPosition1;
    size_t currentPosition2 = slPos[0];
    uint64_t fieldStartTlv = (uint64_t)currentPosition2;
    size_t offsetInTlv = 0;
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    size_t offsetBeforeTlv = offsetInTlv;
    size_t positionBeforeTlv = slPos[0];
    size_t bytesRemainingBeforeTlv = (slLen - positionBeforeTlv);
    bool hasBytesForTlv;
    if (offsetBeforeTlv <= bytesRemainingBeforeTlv) {
      hasBytesForTlv = (4 <= (bytesRemainingBeforeTlv - offsetBeforeTlv));
    }
    else {
      hasBytesForTlv = false;
    }
    uint8_t resultAfterTlv;
    if (hasBytesForTlv) {
      offsetInTlv = (offsetBeforeTlv + 4);
      resultAfterTlv = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterTlv = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterSpecializedWrapper32_1;
    if (resultAfterTlv == EVERPARSE_STATUS_SUCCESS) {
      size_t positionOfTlv = slPos[0];
      size_t positionAfterTlv = (positionOfTlv + 4);
      uint8_t *bytesOfTlv = (slBase + positionOfTlv);
      slPos[0] = positionAfterTlv;
      uint32_t tlv = EverParse3dReadUint32(bytesOfTlv);
      uint64_t src64 = (UlongToPtr(tlv));
      uint64_t readOffset = 0;
      uint64_t writeOffset = 0;
      BOOLEAN failed = ((uint8_t)0U);
      uint64_t sz = (uint64_t)___Len;
      BOOLEAN ok = (ProbeInit("___specialized_WRAPPER_32.tlv", sz, ___Output));
      if (ok != 0) {
        SpecializeDep1Specialized32ProbeTlv((___Len - (uint16_t)5), "___specialized_WRAPPER_32", "tlv", "probe", ctxt, errorHandlerFn, &readOffset, &writeOffset, &failed, src64, sz, ___Output);
      }
      else {
        failed = 1;
      }
      uint64_t b;
      if (failed != 0) {
        (void)(errorHandlerFn("___specialized_WRAPPER_32", "tlv", "probe", 0, ctxt, (uint8_t *)(EverParseStreamOf(___Output)), 0));
        b = 0;
      }
      else {
        b = writeOffset;
      }
      bool actionSuccessTlv;
      if (b != 0) {
        uint8_t *base = (uint8_t *)(EverParseStreamOf(___Output));
        size_t len = (size_t)(EverParseStreamLen(___Output));
        size_t cursor = 0;
        uint8_t res = SpecializeDep1ValidateTlvCore((___Len - (uint16_t)5), ctxt, errorHandlerFn, base, len, &cursor);
        actionSuccessTlv = (res == EVERPARSE_STATUS_SUCCESS);
      }
      else {
        (void)(errorHandlerFn("___specialized_WRAPPER_32", "tlv", EverParse3dErrorReasonOfResult(EVERPARSE_STATUS_ERROR_PROBE_FAILED), EverParse3dLegacyKind(EVERPARSE_STATUS_ERROR_PROBE_FAILED), ctxt, slBase, fieldStartTlv));
        actionSuccessTlv = false;
      }
      if (actionSuccessTlv) {
        resultAfterSpecializedWrapper32_1 = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultAfterSpecializedWrapper32_1 = EVERPARSE_STATUS_ERROR_ACTION_FAILED;
      }
    }
    else {
      resultAfterSpecializedWrapper32_1 = resultAfterTlv;
    }
    if (resultAfterSpecializedWrapper32_1 == EVERPARSE_STATUS_SUCCESS) {
      resultAfterSpecializedWrapper32 = resultAfterSpecializedWrapper32_1;
    }
    else {
      (void)(errorHandlerFn("___specialized_WRAPPER_32", "tlv", EverParse3dErrorReasonOfResult(resultAfterSpecializedWrapper32_1), EverParse3dLegacyKind(resultAfterSpecializedWrapper32_1), ctxt, slBase, fieldStartSpecializedWrapper321));
      resultAfterSpecializedWrapper32 = resultAfterSpecializedWrapper32_1;
    }
  }
  else {
    resultAfterSpecializedWrapper32 = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
  }
  if (resultAfterSpecializedWrapper32 == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterSpecializedWrapper32;
  }
  else {
    (void)(errorHandlerFn("___specialized_WRAPPER_32", "__precondition", EverParse3dErrorReasonOfResult(resultAfterSpecializedWrapper32), EverParse3dLegacyKind(resultAfterSpecializedWrapper32), ctxt, slBase, fieldStartSpecializedWrapper32));
    return resultAfterSpecializedWrapper32;
  }
}

static inline uint8_t SpecializeDep1ValidateWrapperCore(void (*___probe_tlv)(uint16_t, const char *, const char *, const char *, EVERPARSE_APP_CTXT, void (*)(const char *, const char *, const char *, uint64_t, uint8_t *, uint8_t *, uint64_t), uint64_t *, uint64_t *, BOOLEAN *, uint64_t, uint64_t, EVERPARSE_COPY_BUFFER_T), uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartWrapper = (uint64_t)currentPosition;
  /* Validating field __precondition */
  bool preconditionConstraintIsOk = (___Len > (uint16_t)5);
  uint8_t resultAfterWrapper;
  if (preconditionConstraintIsOk) {
    size_t currentPosition1 = slPos[0];
    uint64_t fieldStartWrapper1 = (uint64_t)currentPosition1;
    size_t currentPosition2 = slPos[0];
    uint64_t fieldStartTlv = (uint64_t)currentPosition2;
    size_t offsetInTlv = 0;
    /* Checking that we have enough space for a UINT64, i.e., 8 bytes */
    size_t offsetBeforeTlv = offsetInTlv;
    size_t positionBeforeTlv = slPos[0];
    size_t bytesRemainingBeforeTlv = (slLen - positionBeforeTlv);
    bool hasBytesForTlv;
    if (offsetBeforeTlv <= bytesRemainingBeforeTlv) {
      hasBytesForTlv = (8 <= (bytesRemainingBeforeTlv - offsetBeforeTlv));
    }
    else {
      hasBytesForTlv = false;
    }
    uint8_t resultAfterTlv;
    if (hasBytesForTlv) {
      offsetInTlv = (offsetBeforeTlv + 8);
      resultAfterTlv = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultAfterTlv = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterWrapper_1;
    if (resultAfterTlv == EVERPARSE_STATUS_SUCCESS) {
      size_t positionOfTlv = slPos[0];
      size_t positionAfterTlv = (positionOfTlv + 8);
      uint8_t *bytesOfTlv = (slBase + positionOfTlv);
      slPos[0] = positionAfterTlv;
      uint64_t tlv = EverParse3dReadUint64(bytesOfTlv);
      uint64_t readOffset = 0;
      uint64_t writeOffset = 0;
      BOOLEAN failed = ((uint8_t)0U);
      uint64_t sz = (uint64_t)___Len;
      BOOLEAN ok = (ProbeInit("_WRAPPER.tlv", sz, ___Output));
      if (ok != 0) {
        (void)(___probe_tlv((___Len - (uint16_t)5), "_WRAPPER", "tlv", "probe", ctxt, errorHandlerFn, &readOffset, &writeOffset, &failed, tlv, sz, ___Output));
      }
      else {
        failed = 1;
      }
      uint64_t b;
      if (failed != 0) {
        (void)(errorHandlerFn("_WRAPPER", "tlv", "probe", 0, ctxt, (uint8_t *)(EverParseStreamOf(___Output)), 0));
        b = 0;
      }
      else {
        b = writeOffset;
      }
      bool actionSuccessTlv;
      if (b != 0) {
        uint8_t *base = (uint8_t *)(EverParseStreamOf(___Output));
        size_t len = (size_t)(EverParseStreamLen(___Output));
        size_t cursor = 0;
        uint8_t res = SpecializeDep1ValidateTlvCore((___Len - (uint16_t)5), ctxt, errorHandlerFn, base, len, &cursor);
        actionSuccessTlv = (res == EVERPARSE_STATUS_SUCCESS);
      }
      else {
        (void)(errorHandlerFn("_WRAPPER", "tlv", EverParse3dErrorReasonOfResult(EVERPARSE_STATUS_ERROR_PROBE_FAILED), EverParse3dLegacyKind(EVERPARSE_STATUS_ERROR_PROBE_FAILED), ctxt, slBase, fieldStartTlv));
        actionSuccessTlv = false;
      }
      if (actionSuccessTlv) {
        resultAfterWrapper_1 = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultAfterWrapper_1 = EVERPARSE_STATUS_ERROR_ACTION_FAILED;
      }
    }
    else {
      resultAfterWrapper_1 = resultAfterTlv;
    }
    if (resultAfterWrapper_1 == EVERPARSE_STATUS_SUCCESS) {
      resultAfterWrapper = resultAfterWrapper_1;
    }
    else {
      (void)(errorHandlerFn("_WRAPPER", "tlv", EverParse3dErrorReasonOfResult(resultAfterWrapper_1), EverParse3dLegacyKind(resultAfterWrapper_1), ctxt, slBase, fieldStartWrapper1));
      resultAfterWrapper = resultAfterWrapper_1;
    }
  }
  else {
    resultAfterWrapper = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
  }
  if (resultAfterWrapper == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterWrapper;
  }
  else {
    (void)(errorHandlerFn("_WRAPPER", "__precondition", EverParse3dErrorReasonOfResult(resultAfterWrapper), EverParse3dLegacyKind(resultAfterWrapper), ctxt, slBase, fieldStartWrapper));
    return resultAfterWrapper;
  }
}

static void SpecializeDep1EntryProbeWrapper0Tlv(uint16_t ____arg0, const char * tn, const char * fieldName, const char * fd, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER err, uint64_t *readOffset, uint64_t *writeOffset, BOOLEAN *failed, uint64_t src, uint64_t sz, EVERPARSE_COPY_BUFFER_T dest) {
  (void)____arg0;
  (void)fd;
  BOOLEAN hasFailed = failed[0];
  if (hasFailed != 0) {
    (void)(err(tn, fieldName, "probe_and_copy_init_sz", 0, ctxt, (uint8_t *)(EverParseStreamOf(dest)), 0));
  }
  else {
    uint64_t rd = readOffset[0];
    uint64_t wr = writeOffset[0];
    BOOLEAN ok = (ProbeAndCopy(sz, rd, wr, src, dest));
    if (ok != 0) {
      readOffset[0] = (rd + sz);
      writeOffset[0] = (wr + sz);
    }
    else {
      failed[0] = 1;
    }
  }
}

static uint8_t SpecializeDep1ValidateEntryCore(bool ___Requestor32, uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  if (___Requestor32) {
    /* Validating field w32 */
    size_t currentPosition = slPos[0];
    uint64_t fieldStartEntry = (uint64_t)currentPosition;
    uint8_t resultAfterEntry = SpecializeDep1ValidateSpecializedWrapper32Core(___Len, ___Output, ctxt, errorHandlerFn, slBase, slLen, slPos);
    if (resultAfterEntry == EVERPARSE_STATUS_SUCCESS) {
      return resultAfterEntry;
    }
    else {
      (void)(errorHandlerFn("_ENTRY", "w32", EverParse3dErrorReasonOfResult(resultAfterEntry), EverParse3dLegacyKind(resultAfterEntry), ctxt, slBase, fieldStartEntry));
      return resultAfterEntry;
    }
  }
  else {
    if (___Requestor32 == false) {
      /* Validating field w64 */
      size_t currentPosition_1 = slPos[0];
      uint64_t fieldStartEntry_1 = (uint64_t)currentPosition_1;
      uint8_t resultAfterEntry_1 = SpecializeDep1ValidateWrapperCore(SpecializeDep1EntryProbeWrapper0Tlv, ___Len, ___Output, ctxt, errorHandlerFn, slBase, slLen, slPos);
      if (resultAfterEntry_1 == EVERPARSE_STATUS_SUCCESS) {
        return resultAfterEntry_1;
      }
      else {
        (void)(errorHandlerFn("_ENTRY", "w64", EverParse3dErrorReasonOfResult(resultAfterEntry_1), EverParse3dLegacyKind(resultAfterEntry_1), ctxt, slBase, fieldStartEntry_1));
        return resultAfterEntry_1;
      }
    }
    else {
      size_t scanOffset = 0;
      size_t currentPosition_2 = slPos[0];
      uint64_t streamPositionAtX14 = (uint64_t)currentPosition_2;
      uint64_t startPositionOfX14 = (streamPositionAtX14 + (uint64_t)scanOffset);
      uint8_t resultOfX14 = EVERPARSE_STATUS_ERROR_IMPOSSIBLE;
      uint8_t res;
      if (resultOfX14 == EVERPARSE_STATUS_SUCCESS) {
        res = resultOfX14;
      }
      else {
        (void)(errorHandlerFn("_ENTRY", "_x_14", EverParse3dErrorReasonOfResult(resultOfX14), EverParse3dLegacyKind(resultOfX14), ctxt, slBase, startPositionOfX14));
        res = resultOfX14;
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
  }
}

uint64_t SpecializeDep1ValidateEntry(BOOLEAN ___Requestor32, uint16_t ___Len, EVERPARSE_COPY_BUFFER_T ___Output, uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = SpecializeDep1ValidateEntryCore((___Requestor32 != 0), ___Len, ___Output, ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * 1152921504606846976ULL) + position);
}


