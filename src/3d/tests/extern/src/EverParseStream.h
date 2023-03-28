#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stdint.h>

struct es_cell {
  uint8_t * buf;
  uint64_t len;
  struct es_cell * next;
};

struct EVERPARSE_INPUT_STREAM_BASE_s {
  struct es_cell * head;
};

typedef struct EVERPARSE_INPUT_STREAM_BASE_s * EVERPARSE_INPUT_STREAM_BASE;

EVERPARSE_INPUT_STREAM_BASE EverParseCreate();

int EverParsePush(EVERPARSE_INPUT_STREAM_BASE x, uint8_t * buf, uint64_t len);

// dummy types, they are not used
typedef int EVERPARSE_EXTRA_T;

void EverParseHandleError(EVERPARSE_EXTRA_T _dummy, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
void EverParseRetreat(EVERPARSE_EXTRA_T _dummy, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize);
#endif // __EVERPARSESTREAM
