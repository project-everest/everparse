

#ifndef SpecializeDep1_H
#define SpecializeDep1_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
SpecializeDep1ValidateEntry(
  BOOLEAN Requestor32,
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLen,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define SpecializeDep1_H_DEFINED
#endif /* SpecializeDep1_H */
