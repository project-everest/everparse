

#ifndef SpecializeDep1_H
#define SpecializeDep1_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

void
SpecializeDep1CopyBytes(
  uint64_t Numbytes,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

void
SpecializeDep1Specialized32ProbeUnion(
  uint8_t Tag,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

void
SpecializeDep1Specialized32ProbeTlv(
  uint16_t Len,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

uint8_t
SpecializeDep1ValidateUnion(
  uint8_t Tag,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
SpecializeDep1ValidateTlv(
  uint16_t Len,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
SpecializeDep1ValidateSpecializedWrapper32(
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
SpecializeDep1ValidateWrapper(
  void
  (*ProbeTlv)(
    uint16_t x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    EVERPARSE_STRING x3,
    uint8_t *x4,
    void
    (*x5)(
      EVERPARSE_STRING x0,
      EVERPARSE_STRING x1,
      EVERPARSE_STRING x2,
      uint8_t x3,
      uint8_t *x4,
      uint8_t *x5,
      size_t x6,
      size_t *x7,
      uint64_t x8
    ),
    uint64_t *x6,
    uint64_t *x7,
    BOOLEAN *x8,
    uint64_t x9,
    uint64_t x10,
    EVERPARSE_COPY_BUFFER_T x11
  ),
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

void
SpecializeDep1EntryProbeWrapper0Tlv(
  uint16_t Arg0,
  EVERPARSE_STRING Tn,
  EVERPARSE_STRING Fn,
  EVERPARSE_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

uint8_t
SpecializeDep1ValidateEntry(
  BOOLEAN Requestor32,
  uint16_t Len,
  EVERPARSE_COPY_BUFFER_T Output,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint8_t x3,
    uint8_t *x4,
    uint8_t *x5,
    size_t x6,
    size_t *x7,
    uint64_t x8
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

#if defined(__cplusplus)
}
#endif

#define SpecializeDep1_H_DEFINED
#endif /* SpecializeDep1_H */
