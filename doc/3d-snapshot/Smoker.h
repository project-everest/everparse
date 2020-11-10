

#ifndef __Smoker_H
#define __Smoker_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"




static inline BOOLEAN EverParseIsError(uint64_t positionOrError);

static inline BOOLEAN EverParseIsSuccess(uint64_t positionOrError);

static inline uint64_t
EverParseMaybeSetErrorCode(uint64_t positionOrError, uint64_t positionAtError, uint64_t code);

static inline uint64_t EverParseCheckConstraintOk(BOOLEAN ok, uint64_t position);

static inline uint64_t
EverParseCheckConstraintOkWithFieldId(
  BOOLEAN ok,
  uint64_t startPosition,
  uint64_t endPosition,
  uint64_t fieldId
);

uint64_t SmokerValidateSmoker(uint32_t Uu, uint8_t *Input, uint64_t StartPosition);

#if defined(__cplusplus)
}
#endif

#define __Smoker_H_DEFINED
#endif
