#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stdint.h>

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

#endif // __EVERPARSESTREAM
