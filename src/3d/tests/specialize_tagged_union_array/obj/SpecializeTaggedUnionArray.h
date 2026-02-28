

#ifndef SpecializeTaggedUnionArray_H
#define SpecializeTaggedUnionArray_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

uint64_t
SpecializeTaggedUnionArrayValidateMain(
  BOOLEAN Requestor32,
  uint16_t Count,
  EVERPARSE_COPY_BUFFER_T Out,
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
  uint64_t InputLen,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define SpecializeTaggedUnionArray_H_DEFINED
#endif /* SpecializeTaggedUnionArray_H */
