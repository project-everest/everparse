#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stddef.h>
#include <stdint.h>

/* A client-provided input stream for `3d --pulse --input_stream extern`.

   The Pulse extern backend asks the client for these primitives, all taking
   the stream object alone and using size_t for byte counts:

     BOOLEAN EverParseStreamHasAt(base, off, n)
     BOOLEAN EverParseStreamHas(base, n)
     void    EverParseStreamReadBytes(base, n, dst)
     void    EverParseStreamSkip(base, n)
     size_t  EverParseStreamEmpty(base)
     size_t  EverParseStreamGetPosition(base)

   Two things differ from the Low* extern backend. The stream tracks its own
   position, because the validator takes only the stream object and the
   generated wrapper recovers the parsed size with EverParseStreamGetPosition;
   and ReadBytes always copies rather than returning a possibly-aliasing
   pointer, which costs nothing since it is only ever asked for a leaf integer,
   so at most 8 bytes. */

struct es_cell {
  uint8_t * buf;
  size_t len;
  struct es_cell * next;
};

struct EVERPARSE_INPUT_STREAM_BASE_s {
  struct es_cell * head;
  size_t consumed;
};

typedef struct EVERPARSE_INPUT_STREAM_BASE_s * EVERPARSE_INPUT_STREAM_BASE;

EVERPARSE_INPUT_STREAM_BASE EverParseCreate(void);

int EverParsePush(EVERPARSE_INPUT_STREAM_BASE x, uint8_t * buf, size_t len);

// dummy type, it is not used
typedef int EVERPARSE_EXTRA_T;

void EverParseHandleError(EVERPARSE_EXTRA_T _dummy, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
void EverParseRetreat(EVERPARSE_EXTRA_T _dummy, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize);
#endif // __EVERPARSESTREAM
