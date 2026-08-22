#include "EverParseEndianness.h"
#define EVERPARSE_SUCCESS 0ul
#define EVERPARSE_ERROR_GENERIC 1uL
#define EVERPARSE_ERROR_NOT_ENOUGH_DATA 2uL
#define EVERPARSE_ERROR_IMPOSSIBLE 3uL
#define EVERPARSE_ERROR_LIST_SIZE_NOT_MULTIPLE 4uL
#define EVERPARSE_ERROR_ACTION_FAILED 5uL
#define EVERPARSE_ERROR_CONSTRAINT_FAILED 6uL
#define EVERPARSE_ERROR_UNEXPECTED_PADDING 7uL
// Probe wrapper error codes
#define EVERPARSE_PROBE_FAILURE_INCORRECT_SIZE 256uL
#define EVERPARSE_PROBE_FAILURE_INIT 257uL
#define EVERPARSE_PROBE_FAILURE_PROBE 258uL
#define EVERPARSE_PROBE_FAILURE_VALIDATION 259uL




#ifdef __cplusplus
extern "C" {
#endif
BOOLEAN GotoReturnCheckPoint(uint8_t *base, uint32_t len);

uint32_t GotoReturnProbeInPlaceCheckTagged(uint64_t bound, EVERPARSE_COPY_BUFFER_T probeDest, uint64_t probeAddr, uint64_t providedSize);
#ifdef __cplusplus
}
#endif
