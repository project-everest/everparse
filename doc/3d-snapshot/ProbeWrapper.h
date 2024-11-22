#include "EverParseEndianness.h"
#define EVERPARSE_ERROR_GENERIC 1uL
#define EVERPARSE_ERROR_NOT_ENOUGH_DATA 2uL
#define EVERPARSE_ERROR_IMPOSSIBLE 3uL
#define EVERPARSE_ERROR_LIST_SIZE_NOT_MULTIPLE 4uL
#define EVERPARSE_ERROR_ACTION_FAILED 5uL
#define EVERPARSE_ERROR_CONSTRAINT_FAILED 6uL
#define EVERPARSE_ERROR_UNEXPECTED_PADDING 7uL




#ifdef __cplusplus
extern "C" {
#endif
BOOLEAN ProbeCheckS(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len);

BOOLEAN ProbeCheckU(EVERPARSE_COPY_BUFFER_T destS, EVERPARSE_COPY_BUFFER_T destT, uint8_t *base, uint32_t len);

BOOLEAN ProbeCheckV(EVERPARSE_COPY_BUFFER_T destS, EVERPARSE_COPY_BUFFER_T destT, uint8_t *base, uint32_t len);

BOOLEAN ProbeCheckIndirect(uint8_t *base, uint32_t len);

BOOLEAN ProbeProbeAndCopyCheckIndirect(EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr);

BOOLEAN ProbeCheckI(EVERPARSE_COPY_BUFFER_T dest, uint8_t *base, uint32_t len);

BOOLEAN ProbeProbeAndCopyCheckI(EVERPARSE_COPY_BUFFER_T dest, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr);
#ifdef __cplusplus
}
#endif