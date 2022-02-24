#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stdint.h>

#define KRML_CHECK_SIZE(_typ, _val)

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

#endif // __EVERPARSESTREAM
