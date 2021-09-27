#ifndef __TPoint_OutputTypesDefs_H
#define __TPoint_OutputTypesDefs_H

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct _OPOINT {
    uint8_t   x;
    uint32_t  y;
} OPOINT;

typedef struct _OTPOINT {
    OPOINT    op;
    uint64_t  oz;
} OTPOINT;



#if defined(__cplusplus)
}
#endif

#define __TPoint_OutputTypes_H_DEFINED
#endif
