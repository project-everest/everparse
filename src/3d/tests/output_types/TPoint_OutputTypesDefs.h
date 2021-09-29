#ifndef __TPoint_OutputTypesDefs_H
#define __TPoint_OutputTypesDefs_H

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct _OPoint {
    uint8_t   x;
    uint32_t  y;
} OPoint;

typedef struct _Otpoint {
    OPoint    op;
    uint64_t  oz;
} Otpoint;



#if defined(__cplusplus)
}
#endif

#define __TPoint_OutputTypes_H_DEFINED
#endif
