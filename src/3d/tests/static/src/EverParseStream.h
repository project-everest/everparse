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
typedef int EverParseExtraT;

BOOLEAN _EverParseHas(EverParseExtraT const _unused,  EverParseInputStreamBase const x, uint64_t n);

uint8_t *_EverParseRead(EverParseExtraT const _unused, EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst);

void _EverParseSkip(EverParseExtraT const _unused, EverParseInputStreamBase const x, uint64_t n);

uint64_t _EverParseEmpty(EverParseExtraT const _unused, EverParseInputStreamBase const x);

static inline BOOLEAN EverParseHas(EverParseExtraT const _unused,  EverParseInputStreamBase const x, uint64_t n) {
  return _EverParseHas(_unused, x, n);
}

static inline uint8_t *EverParseRead(EverParseExtraT const _unused, EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst) {
  return _EverParseRead(_unused, x, n, dst);
}

static inline void EverParseSkip(EverParseExtraT const _unused, EverParseInputStreamBase const x, uint64_t n) {
  _EverParseSkip(_unused, x, n);
}

static inline uint64_t EverParseEmpty(EverParseExtraT const _unused, EverParseInputStreamBase const x) {
  return _EverParseEmpty(_unused, x);
}

#endif // __EVERPARSESTREAM
