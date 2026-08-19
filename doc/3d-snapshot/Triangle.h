

#ifndef Triangle_H
#define Triangle_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
TriangleValidateTriangle(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define Triangle_H_DEFINED
#endif /* Triangle_H */
