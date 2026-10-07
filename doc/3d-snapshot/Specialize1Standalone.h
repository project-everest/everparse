

#ifndef Specialize1Standalone_H
#define Specialize1Standalone_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
Specialize1standaloneValidateR(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define Specialize1Standalone_H_DEFINED
#endif /* Specialize1Standalone_H */
