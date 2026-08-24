#ifndef __EVERPARSESTREAM
#define __EVERPARSESTREAM

#include <stddef.h>
#include <stdint.h>
#include "EverParsePulseEndianness.h"

/* A client-provided input stream for `3d --pulse --input_stream static`, where
   the stream operations are reached through function pointers rather than
   being linked directly.

   In Low* the vtable lives in EVERPARSE_EXTRA_T, the application context, which
   is threaded through every stream primitive. Under --pulse the primitives take
   only the stream, deliberately: the application context is a concern of the
   error handler, not of the stream. So the vtable lives in the stream object
   instead, and the primitives KaRaMeL declares dispatch through it. The test is
   unchanged in substance -- no stream operation is resolved at link time. */

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
  size_t consumed;
  EVERPARSE_STREAM_VTABLE vtable;
};

typedef struct EVERPARSE_INPUT_STREAM_BASE_s * EVERPARSE_INPUT_STREAM_BASE;

EVERPARSE_INPUT_STREAM_BASE EverParseCreate(EVERPARSE_STREAM_VTABLE vtable);

size_t EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE x);

int EverParsePush(EVERPARSE_INPUT_STREAM_BASE x, uint8_t * buf, size_t len);

/* The application context is now only what the error handler needs. */
typedef struct {
  void *errorContext;
  void (*handleError) (void *errorContext, uint64_t pos, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
} EVERPARSE_EXTRA_T;

void EverParseHandleError(EVERPARSE_EXTRA_T f, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code);
void EverParseRetreat(EVERPARSE_EXTRA_T f, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize);

#endif // __EVERPARSESTREAM
