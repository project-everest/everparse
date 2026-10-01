#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stddef.h>
#include <stdint.h>

/* A client-provided input stream for `3d --pulse --input_stream extern`.

   The Pulse extern backend asks the client for these primitives. As in the
   Low* extern backend, each one receives the client context EVERPARSE_EXTRA_T
   that was passed to the validator; byte counts are size_t:

     BOOLEAN EverParseStreamHasAt(extra, base, off, n)
     BOOLEAN EverParseStreamHas(extra, base, n)
     void    EverParseStreamReadBytes(extra, base, n, dst)
     void    EverParseStreamSkip(extra, base, n)
     size_t  EverParseStreamEmpty(extra, base)
     uint64_t EverParseStreamGetPosition(base)

   Two things differ from the Low* extern backend. The stream tracks its own
   position, exposed by the extra Pulse-only primitive
   EverParseStreamGetPosition: the validator takes only the stream object, so
   the generated wrapper recovers the parsed size from the stream. That
   primitive takes no context, because it is also called from the generated
   DefaultErrorHandler, whose signature has none. And ReadBytes always copies
   rather than returning a possibly-aliasing pointer, which costs nothing
   since it is only ever asked for a leaf integer, so at most 8 bytes. */

struct es_cell {
  uint8_t * buf;
  size_t len;
  struct es_cell * next;
};

struct EVERPARSE_INPUT_STREAM_BASE_s {
  struct es_cell * head;
  uint64_t consumed;
};

typedef struct EVERPARSE_INPUT_STREAM_BASE_s * EVERPARSE_INPUT_STREAM_BASE;

EVERPARSE_INPUT_STREAM_BASE EverParseCreate(void);

int EverParsePush(EVERPARSE_INPUT_STREAM_BASE x, uint8_t * buf, size_t len);

/* The client context threaded through the validator down to the stream
   primitives above. This test only checks that it arrives intact. */
typedef int EVERPARSE_EXTRA_T;

/* Number of errors reported through EverParseHandleError so far. The tests in
   main.c read it to recover the accept/reject verdict: the generated wrapper
   returns the parsed size, which is nonzero on failure too. */
extern int EverParseErrorCount;

/* A sentinel context value. main.c passes it to every validator, and each
   stream primitive checks that it arrives intact, so that a backend which
   silently dropped EVERPARSE_EXTRA_T would fail this test rather than pass it
   unnoticed. */
#define EVERPARSE_EXTRA_COOKIE 0x5EED
void EverParseCheckExtra(EVERPARSE_EXTRA_T extra);

void EverParseHandleError(EVERPARSE_EXTRA_T _dummy, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
void EverParseRetreat(EVERPARSE_EXTRA_T _dummy, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize);
#endif // __EVERPARSESTREAM
