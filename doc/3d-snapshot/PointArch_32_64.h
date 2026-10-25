

#ifndef PointArch_32_64_H
#define PointArch_32_64_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "arch_flags.h"
#include "EverParse.h"

uint64_t
PointArch3264ValidatePoint(
  uint8_t *Ctxt,
  void
  (*Handler)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t Length,
  uint64_t Start
);

#if defined(__cplusplus)
}
#endif

#define PointArch_32_64_H_DEFINED
#endif /* PointArch_32_64_H */
