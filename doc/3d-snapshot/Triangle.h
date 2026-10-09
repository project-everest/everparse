

#ifndef Triangle_H
#define Triangle_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
TriangleValidateTriangle(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define Triangle_H_DEFINED
#endif /* Triangle_H */
