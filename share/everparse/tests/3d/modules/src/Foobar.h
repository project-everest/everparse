#include <stdint.h>
#ifndef C_ASSERT
#define C_ASSERT(e) typedef char __C_ASSERT__[(e)?1:-1]
#endif
typedef struct _CIRCLE {
    uint32_t p[4];
    uint32_t radius;
} CIRCLE;
