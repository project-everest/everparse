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

typedef struct {
  BOOLEAN (*has)(EverParseInputStreamBase const x, uint64_t n);
  uint8_t * (*read)(EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst);
  void (*skip)(EverParseInputStreamBase const x, uint64_t n);
  uint64_t (*empty)(EverParseInputStreamBase const x);
} EverParseExtraT;

static inline BOOLEAN EverParseHas(EverParseExtraT const f,  EverParseInputStreamBase const x, uint64_t n) {
  return f.has(x, n);
}

static inline uint8_t *EverParseRead(EverParseExtraT const f, EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst) {
  return f.read(x, n, dst);
}

static inline void EverParseSkip(EverParseExtraT const f, EverParseInputStreamBase const x, uint64_t n) {
  f.skip(x, n);
}

static inline uint64_t EverParseEmpty(EverParseExtraT const f, EverParseInputStreamBase const x) {
  return f.empty(x);
}

#endif // __EVERPARSESTREAM
