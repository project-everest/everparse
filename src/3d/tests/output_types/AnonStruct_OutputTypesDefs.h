#ifndef __AnonStruct_OutputTypesDefs_H
#define __AnonStruct_OutputTypesDefs_H

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct _OTPOINT {
  uint32_t     x;
  struct {
    uint32_t   y;
    uint32_t   z;
  };
} OTPOINT;

#if defined(__cplusplus)
}
#endif

#define __TPoint_OutputTypes_H_DEFINED
#endif
