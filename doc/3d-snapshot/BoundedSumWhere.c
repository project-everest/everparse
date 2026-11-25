#include "BoundedSumWhere.h"

static uint8_t BoundedSumWhereValidateBoundedSumCore(uint32_t bound, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos);

static uint8_t BoundedSumWhereValidateBoundedSumCore(uint32_t bound, EVERPARSE_APP_CTXT ctxt, EVERPARSE_ERROR_HANDLER errorHandlerFn, uint8_t *slBase, size_t slLen, size_t *slPos) {
  size_t currentPosition = slPos[0];
  uint64_t fieldStartBoundedSum = (uint64_t)currentPosition;
  /* Validating field __precondition */
  bool preconditionConstraintIsOk = (bound <= (uint32_t)1729);
  uint8_t resultAfterBoundedSum;
  if (preconditionConstraintIsOk) {
    size_t offsetInLeft = 0;
    size_t currentPosition1 = slPos[0];
    uint64_t streamPositionAtLeft = (uint64_t)currentPosition1;
    size_t offsetOfLeft = offsetInLeft;
    uint64_t startPositionOfLeft = (streamPositionAtLeft + (uint64_t)offsetOfLeft);
    /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
    size_t offsetBeforeLeft = offsetInLeft;
    size_t positionBeforeLeft = slPos[0];
    size_t bytesRemainingBeforeLeft = (slLen - positionBeforeLeft);
    bool hasBytesForLeft;
    if (offsetBeforeLeft <= bytesRemainingBeforeLeft) {
      hasBytesForLeft = (4 <= (bytesRemainingBeforeLeft - offsetBeforeLeft));
    }
    else {
      hasBytesForLeft = false;
    }
    uint8_t resultOfLeft;
    if (hasBytesForLeft) {
      offsetInLeft = (offsetBeforeLeft + 4);
      resultOfLeft = EVERPARSE_STATUS_SUCCESS;
    }
    else {
      resultOfLeft = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
    }
    uint8_t resultAfterLeft;
    if (resultOfLeft == EVERPARSE_STATUS_SUCCESS) {
      resultAfterLeft = resultOfLeft;
    }
    else {
      (void)(errorHandlerFn("_boundedSum", "left", EverParse3dErrorReasonOfResult(resultOfLeft), EverParse3dLegacyKind(resultOfLeft), ctxt, slBase, startPositionOfLeft));
      resultAfterLeft = resultOfLeft;
    }
    if (resultAfterLeft == EVERPARSE_STATUS_SUCCESS) {
      size_t positionOfLeft = slPos[0];
      size_t positionAfterLeft = (positionOfLeft + 4);
      uint8_t *bytesOfLeft = (slBase + positionOfLeft);
      slPos[0] = positionAfterLeft;
      uint32_t left = EverParse3dReadUint32(bytesOfLeft);
      /* Validating field right */
      size_t currentPosition2 = slPos[0];
      uint64_t fieldStartBoundedSum1 = (uint64_t)currentPosition2;
      size_t offsetInRightRefinement = 0;
      /* Checking that we have enough space for a UINT32, i.e., 4 bytes */
      size_t offsetBeforeRightRefinement = offsetInRightRefinement;
      size_t positionBeforeRightRefinement = slPos[0];
      size_t bytesRemainingBeforeRightRefinement = (slLen - positionBeforeRightRefinement);
      bool hasBytesForRightRefinement;
      if (offsetBeforeRightRefinement <= bytesRemainingBeforeRightRefinement) {
        hasBytesForRightRefinement = (4 <= (bytesRemainingBeforeRightRefinement - offsetBeforeRightRefinement));
      }
      else {
        hasBytesForRightRefinement = false;
      }
      uint8_t resultAfterRightRefinement;
      if (hasBytesForRightRefinement) {
        offsetInRightRefinement = (offsetBeforeRightRefinement + 4);
        resultAfterRightRefinement = EVERPARSE_STATUS_SUCCESS;
      }
      else {
        resultAfterRightRefinement = EVERPARSE_STATUS_ERROR_NOT_ENOUGH_DATA;
      }
      uint8_t resultAfterBoundedSum_1;
      if (resultAfterRightRefinement == EVERPARSE_STATUS_SUCCESS) {
        /* reading field_value */
        size_t positionOfRightRefinement = slPos[0];
        size_t positionAfterRightRefinement = (positionOfRightRefinement + 4);
        uint8_t *bytesOfRightRefinement = (slBase + positionOfRightRefinement);
        slPos[0] = positionAfterRightRefinement;
        uint32_t rightRefinement = EverParse3dReadUint32(bytesOfRightRefinement);
        /* start: checking constraint */
        bool rightRefinementConstraintIsOk = ((left <= bound) && (rightRefinement <= (bound - left)));
        /* end: checking constraint */
        if (rightRefinementConstraintIsOk) {
          resultAfterBoundedSum_1 = EVERPARSE_STATUS_SUCCESS;
        }
        else {
          resultAfterBoundedSum_1 = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
        }
      }
      else {
        resultAfterBoundedSum_1 = resultAfterRightRefinement;
      }
      if (resultAfterBoundedSum_1 == EVERPARSE_STATUS_SUCCESS) {
        resultAfterBoundedSum = resultAfterBoundedSum_1;
      }
      else {
        (void)(errorHandlerFn("_boundedSum", "right.refinement", EverParse3dErrorReasonOfResult(resultAfterBoundedSum_1), EverParse3dLegacyKind(resultAfterBoundedSum_1), ctxt, slBase, fieldStartBoundedSum1));
        resultAfterBoundedSum = resultAfterBoundedSum_1;
      }
    }
    else {
      resultAfterBoundedSum = resultAfterLeft;
    }
  }
  else {
    resultAfterBoundedSum = EVERPARSE_STATUS_ERROR_CONSTRAINT_FAILED;
  }
  if (resultAfterBoundedSum == EVERPARSE_STATUS_SUCCESS) {
    return resultAfterBoundedSum;
  }
  else {
    (void)(errorHandlerFn("_boundedSum", "__precondition", EverParse3dErrorReasonOfResult(resultAfterBoundedSum), EverParse3dLegacyKind(resultAfterBoundedSum), ctxt, slBase, fieldStartBoundedSum));
    return resultAfterBoundedSum;
  }
}

uint64_t BoundedSumWhereValidateBoundedSum(uint32_t bound, uint8_t *ctxt, EVERPARSE_ERROR_HANDLER handler, uint8_t *input, uint64_t length, uint64_t start) {
  size_t len = (size_t)length;
  size_t initial = (size_t)start;
  size_t cursor = initial;
  uint8_t status = BoundedSumWhereValidateBoundedSumCore(bound, ctxt, handler, input, len, &cursor);
  uint64_t position = (uint64_t)cursor;
  return ((EverParse3dLegacyKind(status) * EVERPARSE_VALIDATOR_ERROR_GENERIC) + position);
}


