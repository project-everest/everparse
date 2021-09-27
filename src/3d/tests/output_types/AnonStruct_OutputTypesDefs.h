#ifndef __AnonStruct_OutputTypesDefs_H
#define __AnonStruct_OutputTypesDefs_H

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct _OTPOINT {
  uint8_t     x;
  struct {
    uint8_t   y;
    uint8_t   z;
  };
} OTPOINT;

#if defined(__cplusplus)
}
#endif

#define __TPoint_OutputTypes_H_DEFINED
#endif
