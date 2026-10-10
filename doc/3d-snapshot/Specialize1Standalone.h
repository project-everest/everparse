

#ifndef Specialize1Standalone_H
#define Specialize1Standalone_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

void
Specialize1standaloneCopyBytes(
  uint64_t Numbytes,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

void
Specialize1standaloneSkipBytesWrite(
  uint64_t Numbytes,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

void
Specialize1standaloneReadAndCoercePointer(
  PRIMS_STRING Fieldname,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

void
Specialize1standaloneSpecialized32ProbeS64(
  uint32_t Bound,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

uint8_t
Specialize1standaloneValidateCoreT(
  uint32_t Bound,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
Specialize1standaloneValidateCoreS64(
  void
  (*ProbePtrT)(
    uint32_t x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    PRIMS_STRING x3,
    uint8_t *x4,
    void
    (*x5)(
      PRIMS_STRING x0,
      PRIMS_STRING x1,
      PRIMS_STRING x2,
      uint64_t x3,
      uint8_t *x4,
      uint8_t *x5,
      uint64_t x6
    ),
    uint64_t *x6,
    uint64_t *x7,
    BOOLEAN *x8,
    uint64_t x9,
    uint64_t x10,
    EVERPARSE_COPY_BUFFER_T x11
  ),
  uint32_t Bound,
  EVERPARSE_COPY_BUFFER_T Dest,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

void
Specialize1standaloneSpecialized32ProbeT(
  uint32_t Bound,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

uint8_t
Specialize1standaloneValidateCoreSpecializedR32(
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint8_t
Specialize1standaloneValidateCoreR64(
  void
  (*ProbeS640)(
    uint32_t x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    PRIMS_STRING x3,
    uint8_t *x4,
    void
    (*x5)(
      PRIMS_STRING x0,
      PRIMS_STRING x1,
      PRIMS_STRING x2,
      uint64_t x3,
      uint8_t *x4,
      uint8_t *x5,
      uint64_t x6
    ),
    uint64_t *x6,
    uint64_t *x7,
    BOOLEAN *x8,
    uint64_t x9,
    uint64_t x10,
    EVERPARSE_COPY_BUFFER_T x11
  ),
  void
  (*ProbePtrS)(
    uint32_t x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    PRIMS_STRING x3,
    uint8_t *x4,
    void
    (*x5)(
      PRIMS_STRING x0,
      PRIMS_STRING x1,
      PRIMS_STRING x2,
      uint64_t x3,
      uint8_t *x4,
      uint8_t *x5,
      uint64_t x6
    ),
    uint64_t *x6,
    uint64_t *x7,
    BOOLEAN *x8,
    uint64_t x9,
    uint64_t x10,
    EVERPARSE_COPY_BUFFER_T x11
  ),
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

void
Specialize1standaloneRProbeFieldR640T(
  uint32_t Arg0,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

void
Specialize1standaloneRProbeFieldR641S64(
  uint32_t Arg0,
  PRIMS_STRING Tn,
  PRIMS_STRING Fn,
  PRIMS_STRING Fd,
  uint8_t *Ctxt,
  void
  (*Err)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint64_t *ReadOffset,
  uint64_t *WriteOffset,
  BOOLEAN *Failed,
  uint64_t Src,
  uint64_t Sz,
  EVERPARSE_COPY_BUFFER_T Dest
);

uint8_t
Specialize1standaloneValidateCoreR(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    PRIMS_STRING x0,
    PRIMS_STRING x1,
    PRIMS_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *SlBase,
  size_t SlLen,
  size_t *SlPos
);

uint64_t
Specialize1standaloneValidateR(
  BOOLEAN Requestor32,
  EVERPARSE_COPY_BUFFER_T DestS,
  EVERPARSE_COPY_BUFFER_T DestT,
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

#define Specialize1Standalone_H_DEFINED
#endif /* Specialize1Standalone_H */
