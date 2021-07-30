#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stdint.h>

struct es_cell {
  uint8_t * buf;
  uint8_t len;
  struct es_cell * next;
};

struct EverParseInputStreamBase_s {
  struct es_cell * head;
};

typedef struct EverParseInputStreamBase_s * EverParseInputStreamBase;

EverParseInputStreamBase EverParseCreate();

int EverParsePush(EverParseInputStreamBase x, uint8_t * buf, uint32_t len);

#endif // __EVERPARSESTREAM
