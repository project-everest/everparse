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
BOOLEAN GetFieldPtrCheckT(uint8_t** out, uint8_t *base, uint32_t len);

BOOLEAN GetFieldPtrCheckTact(uint8_t** out, uint8_t *base, uint32_t len);
#ifdef __cplusplus
}
#endif
