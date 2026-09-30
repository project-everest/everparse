#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stddef.h>
#include <stdint.h>
#include "EverParseEndianness.h"

/* A client-provided input stream for `3d --pulse --input_stream static`.

   `static` and `extern` are one F* development, so they ask the client for the
   same primitives. As in Low*, each one receives the client context
   EVERPARSE_EXTRA_T that was passed to the validator:

     BOOLEAN  EverParseStreamHasAt(extra, base, off, n)
     BOOLEAN  EverParseStreamHas(extra, base, n)
     void     EverParseStreamReadBytes(extra, base, n, dst)
     void     EverParseStreamSkip(extra, base, n)
     size_t   EverParseStreamEmpty(extra, base)
     size_t   EverParseStreamGetPosition(base)
     BOOLEAN  EverParseFieldPtrAfterImpl(extra, sz, out, base)

   EverParseFieldPtrAfterImpl backs the field_ptr_after action, which `buffer`
   does not have. EverParseStreamGetPosition is the one primitive that takes no
   context, because it is also called from the generated DefaultErrorHandler,
   whose signature has none.

   Note on `static` under --pulse, and why this file defines the primitives.
   The two backends differ in the C linkage of these primitives: under
   `static` the generated EverParse.h declares each one `static inline`, so the
   compiler sees the stream operation at every validator call site instead of
   linking against it. That makes it the *client's* job to provide a definition
   in every translation unit, which is what `--input_stream_include` is for:
   this header is included into each generated .c file. As in the Low* static
   test (src/3d/tests/static/src/EverParseStream.h), the real bodies stay in
   EverParseStream.c under `_`-prefixed names and this header only adds thin
   `static inline` forwarders.

   EverParseNullPtr is the exception: it is an assumed *value*, so it stays a
   plain `extern` under both backends and is defined once in EverParseStream.c.

   Unlike Low*, the stream tracks its own position (the validator takes only the
   stream object, and the generated wrapper recovers the parsed size with
   EverParseStreamGetPosition), byte counts are size_t, and ReadBytes always
   copies rather than returning a possibly-aliasing pointer. */

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

uint8_t *EverParseStreamPeep(EVERPARSE_INPUT_STREAM_BASE x, size_t n);

/* The client context threaded through the validator down to the stream
   primitives above. This test only checks that it arrives intact. */
typedef int EVERPARSE_EXTRA_T;

/* A sentinel context value. main.c passes it to every validator, and each
   stream primitive checks that it arrives intact, so that a backend which
   silently dropped EVERPARSE_EXTRA_T would fail this test rather than pass it
   unnoticed. */
#define EVERPARSE_EXTRA_COOKIE 0x5EED
void EverParseCheckExtra(EVERPARSE_EXTRA_T extra);

/* The assumed stream primitives. Under `--input_stream static` the generated
   EverParse.h declares these `static inline`, so each translation unit that
   includes this header needs a definition of its own. */

BOOLEAN _EverParseStreamHas(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t n);
BOOLEAN _EverParseStreamHasAt(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t off, size_t n);
size_t _EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE x);
void _EverParseStreamReadBytes(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t n, uint8_t *dst);
void _EverParseStreamSkip(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t n);
size_t _EverParseStreamEmpty(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x);
BOOLEAN _EverParseFieldPtrAfterImpl(EVERPARSE_EXTRA_T extra, uint64_t sz, uint8_t **out, EVERPARSE_INPUT_STREAM_BASE x);

static inline BOOLEAN EverParseStreamHas(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t n) {
  return _EverParseStreamHas(extra, x, n);
}

static inline BOOLEAN EverParseStreamHasAt(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t off, size_t n) {
  return _EverParseStreamHasAt(extra, x, off, n);
}

static inline size_t EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE x) {
  return _EverParseStreamGetPosition(x);
}

static inline void EverParseStreamReadBytes(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t n, uint8_t *dst) {
  _EverParseStreamReadBytes(extra, x, n, dst);
}

static inline void EverParseStreamSkip(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t n) {
  _EverParseStreamSkip(extra, x, n);
}

static inline size_t EverParseStreamEmpty(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x) {
  return _EverParseStreamEmpty(extra, x);
}

static inline BOOLEAN EverParseFieldPtrAfterImpl(EVERPARSE_EXTRA_T extra, uint64_t sz, uint8_t **out, EVERPARSE_INPUT_STREAM_BASE x) {
  return _EverParseFieldPtrAfterImpl(extra, sz, out, x);
}

void EverParseHandleError(EVERPARSE_EXTRA_T _dummy, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
void EverParseRetreat(EVERPARSE_EXTRA_T _dummy, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize);

#endif // __EVERPARSESTREAM
