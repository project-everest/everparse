

#ifndef SpecializeTaggedUnionArray_ExternalAPI_H
#define SpecializeTaggedUnionArray_ExternalAPI_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

extern BOOLEAN
ProbeAndCopy(uint64_t uu___, uint64_t x0, uint64_t x1, uint64_t x2, EVERPARSE_COPY_BUFFER_T x3);

extern uint16_t
ProbeAndReadU16(BOOLEAN *uu___, uint64_t x0, uint64_t x1, EVERPARSE_COPY_BUFFER_T x2);

extern BOOLEAN WriteU16(uint16_t uu___, uint64_t x0, EVERPARSE_COPY_BUFFER_T x1);

extern uint32_t
ProbeAndReadU32(BOOLEAN *uu___, uint64_t x0, uint64_t x1, EVERPARSE_COPY_BUFFER_T x2);

extern BOOLEAN WriteU32(uint32_t uu___, uint64_t x0, EVERPARSE_COPY_BUFFER_T x1);

extern uint64_t
ProbeAndReadU64(BOOLEAN *uu___, uint64_t x0, uint64_t x1, EVERPARSE_COPY_BUFFER_T x2);

extern BOOLEAN WriteU64(uint64_t uu___, uint64_t x0, EVERPARSE_COPY_BUFFER_T x1);

extern BOOLEAN ProbeInit(EVERPARSE_STRING uu___, uint64_t x0, EVERPARSE_COPY_BUFFER_T x1);

extern uint64_t UlongToPtr(uint32_t ptr);

#if defined(__cplusplus)
}
#endif

#define SpecializeTaggedUnionArray_ExternalAPI_H_DEFINED
#endif /* SpecializeTaggedUnionArray_ExternalAPI_H */
