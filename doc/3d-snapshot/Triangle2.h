

#ifndef Triangle2_H
#define Triangle2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
Triangle2ValidateTriangle(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define Triangle2_H_DEFINED
#endif /* Triangle2_H */
