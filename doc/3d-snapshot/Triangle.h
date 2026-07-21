

#ifndef Triangle_H
#define Triangle_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
TriangleValidateTriangle(
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define Triangle_H_DEFINED
#endif /* Triangle_H */
