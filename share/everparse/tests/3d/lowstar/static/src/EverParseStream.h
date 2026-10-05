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

// dummy types, they are not used
typedef int EVERPARSE_EXTRA_T;

BOOLEAN _EverParseHas(EVERPARSE_EXTRA_T const _unused,  EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n);

uint8_t *_EverParseRead(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n, uint8_t * const dst);

void _EverParseSkip(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n);

uint64_t _EverParseEmpty(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x);

uint8_t * _EverParsePeep(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE x, uint64_t n);

static inline BOOLEAN EverParseHas(EVERPARSE_EXTRA_T const _unused,  EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n) {
  return _EverParseHas(_unused, x, n);
}

static inline uint8_t *EverParseRead(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n, uint8_t * const dst) {
  return _EverParseRead(_unused, x, n, dst);
}

static inline void EverParseSkip(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n) {
  _EverParseSkip(_unused, x, n);
}

static inline uint64_t EverParseEmpty(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x) {
  return _EverParseEmpty(_unused, x);
}

static inline uint8_t
*EverParsePeep(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE x, uint64_t n) {
  return _EverParsePeep(_unused, x, n);
}



static inline
void EverParseHandleError(EVERPARSE_EXTRA_T _dummy, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code)
{
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", typename, fieldname, reason);
}

static inline
void EverParseRetreat(EVERPARSE_EXTRA_T _dummy, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize)
{
}

#endif // __EVERPARSESTREAM
