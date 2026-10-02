#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stddef.h>
#include <stdint.h>
#include "EverParseEndianness.h"

/* A client-provided input stream for `3d --api pulse --input_stream static`, where
   the stream operations are reached through function pointers rather than
   being linked directly.

   In Low* the vtable lives in EVERPARSE_EXTRA_T, the application context. Here
   it lives in the stream object instead, so that the indirection is exercised
   independently of how the context is threaded. The test is unchanged in
   substance -- no stream operation is resolved at link time.

   As in ../../static/src/EverParseStream.h, the primitives receive the client
   context EVERPARSE_EXTRA_T (all but EverParseStreamGetPosition, which is also
   called from the generated DefaultErrorHandler, whose signature has none), and
   `--input_stream static` makes the generated EverParse.h declare each one
   `static inline`. That requires a definition in every translation unit, so the
   real bodies stay in EverParseStream.c under `_`-prefixed names and this
   header only adds thin `static inline` forwarders. */

struct es_cell {
  uint8_t * buf;
  size_t len;
  struct es_cell * next;
};

struct EVERPARSE_INPUT_STREAM_BASE_s;

/* The operations the client plugs in. These mirror the primitives the
   generated code calls, minus the position bookkeeping, which the wrapper
   around them does. */
typedef struct {
  BOOLEAN (*has)(struct EVERPARSE_INPUT_STREAM_BASE_s *x, size_t n);
  BOOLEAN (*hasAt)(struct EVERPARSE_INPUT_STREAM_BASE_s *x, size_t off, size_t n);
  void (*readBytes)(struct EVERPARSE_INPUT_STREAM_BASE_s *x, size_t n, uint8_t *dst);
  void (*skip)(struct EVERPARSE_INPUT_STREAM_BASE_s *x, size_t n);
  size_t (*empty)(struct EVERPARSE_INPUT_STREAM_BASE_s *x);
  uint8_t * (*peep)(struct EVERPARSE_INPUT_STREAM_BASE_s *x, size_t n);
} EVERPARSE_STREAM_VTABLE;

struct EVERPARSE_INPUT_STREAM_BASE_s {
  struct es_cell * head;
  uint64_t consumed;
  EVERPARSE_STREAM_VTABLE vtable;
};

typedef struct EVERPARSE_INPUT_STREAM_BASE_s * EVERPARSE_INPUT_STREAM_BASE;

EVERPARSE_INPUT_STREAM_BASE EverParseCreate(EVERPARSE_STREAM_VTABLE vtable);

int EverParsePush(EVERPARSE_INPUT_STREAM_BASE x, uint8_t * buf, size_t len);

/* The application context is what the error handler needs, and is also
   threaded down to the stream primitives. */
typedef struct {
  void *errorContext;
  void (*handleError) (void *errorContext, uint64_t pos, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
} EVERPARSE_EXTRA_T;

/* The assumed stream primitives. Real bodies live in EverParseStream.c; the
   `static inline` forwarders below are what `--input_stream static` needs in
   every translation unit. */

BOOLEAN _EverParseStreamHas(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t n);
BOOLEAN _EverParseStreamHasAt(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE x, size_t off, size_t n);
uint64_t _EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE x);
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

static inline uint64_t EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE x) {
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

void EverParseHandleError(EVERPARSE_EXTRA_T f, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
void EverParseRetreat(EVERPARSE_EXTRA_T f, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize);

#endif // __EVERPARSESTREAM
