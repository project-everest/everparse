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

typedef BOOLEAN (*EverParseHasT)(EverParseInputStreamBase const x, uint64_t n);

typedef uint8_t * (*EverParseReadT)(EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst);

typedef void (*EverParseSkipT)(EverParseInputStreamBase const x, uint64_t n);

typedef uint64_t (*EverParseEmptyT)(EverParseInputStreamBase const x);

static inline BOOLEAN EverParseHas(EverParseHasT const f,  EverParseInputStreamBase const x, uint64_t n) {
  return f(x, n);
}

static inline uint8_t *EverParseRead(EverParseReadT const f, EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst) {
  return f(x, n, dst);
}

static inline void EverParseSkip(EverParseSkipT const f, EverParseInputStreamBase const x, uint64_t n) {
  f(x, n);
}

static inline uint64_t EverParseEmpty(EverParseEmptyT const f, EverParseInputStreamBase const x) {
  return f(x);
}

#endif // __EVERPARSESTREAM
