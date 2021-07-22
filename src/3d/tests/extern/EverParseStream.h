#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stdint.h>

struct es_cell {
  uint8_t * buf;
  uint8_t len;
  struct es_cell * next;
};

typedef struct es_cell ** EverParseInputStreamBase;

#include "EverParse.h"

#endif // __EVERPARSESTREAM
