#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stdint.h>
#include "EverParseEndianness.h"

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

typedef struct {
  BOOLEAN (*has)(EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n);
  uint8_t * (*read)(EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n, uint8_t * const dst);
  void (*skip)(EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n);
  uint64_t (*empty)(EVERPARSE_INPUT_STREAM_BASE const x);
  void (*retreat)(EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n);
  void *errorContext;
  void (*handleError) (void *errorContext, uint64_t pos, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
} EVERPARSE_EXTRA_T;

static inline BOOLEAN EverParseHas(EVERPARSE_EXTRA_T const f,  EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n) {
  return f.has(x, n);
}

static inline uint8_t *EverParseRead(EVERPARSE_EXTRA_T const f, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n, uint8_t * const dst) {
  return f.read(x, n, dst);
}

static inline void EverParseSkip(EVERPARSE_EXTRA_T const f, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n) {
  f.skip(x, n);
}

static inline uint64_t EverParseEmpty(EVERPARSE_EXTRA_T const f, EVERPARSE_INPUT_STREAM_BASE const x) {
  return f.empty(x);
}

static inline void EverParseHandleError(EVERPARSE_EXTRA_T const f, uint64_t pos, const char *typename, const char *fieldname, const char *reason, uint64_t error_code)
{
  f.handleError(f.errorContext, pos, typename, fieldname, reason, error_code);
}

static inline void EverParseRetreat(EVERPARSE_EXTRA_T const f, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t pos)
{
  f.retreat(x, pos);
}

#endif // __EVERPARSESTREAM
