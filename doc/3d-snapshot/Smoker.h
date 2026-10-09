

#ifndef Smoker_H
#define Smoker_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint8_t
SmokerValidateSmoker(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define Smoker_H_DEFINED
#endif /* Smoker_H */
