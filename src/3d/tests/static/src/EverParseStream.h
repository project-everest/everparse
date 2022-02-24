#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stdint.h>
#include "EverParseEndianness.h"

struct es_cell {
  uint8_t * buf;
  uint64_t len;
  struct es_cell * next;
};

struct EverParseInputStreamBase_s {
  struct es_cell * head;
};

typedef struct EverParseInputStreamBase_s * EverParseInputStreamBase;

EverParseInputStreamBase EverParseCreate();

int EverParsePush(EverParseInputStreamBase x, uint8_t * buf, uint64_t len);

// dummy types, they are not used
typedef int EverParseHasT;
typedef int EverParseReadT;
typedef int EverParseSkipT;
typedef int EverParseEmptyT;

BOOLEAN _EverParseHas(EverParseHasT const _unused,  EverParseInputStreamBase const x, uint64_t n);

uint8_t *_EverParseRead(EverParseReadT const _unused, EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst);

void _EverParseSkip(EverParseSkipT const _unused, EverParseInputStreamBase const x, uint64_t n);

uint64_t _EverParseEmpty(EverParseEmptyT const _unused, EverParseInputStreamBase const x);

static inline BOOLEAN EverParseHas(EverParseHasT const _unused,  EverParseInputStreamBase const x, uint64_t n) {
  return _EverParseHas(_unused, x, n);
}

static inline uint8_t *EverParseRead(EverParseReadT const _unused, EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst) {
  return _EverParseRead(_unused, x, n, dst);
}

static inline void EverParseSkip(EverParseSkipT const _unused, EverParseInputStreamBase const x, uint64_t n) {
  _EverParseSkip(_unused, x, n);
}

static inline uint64_t EverParseEmpty(EverParseEmptyT const _unused, EverParseInputStreamBase const x) {
  return _EverParseEmpty(_unused, x);
}

#endif // __EVERPARSESTREAM
