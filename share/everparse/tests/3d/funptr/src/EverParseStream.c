#include "EverParseEndianness.h"
#include "EverParseStream.h"
#include <stdlib.h>

/* The primitives the generated code calls, reached through the `static inline`
   forwarders in EverParseStream.h. Each one only keeps the position up to date
   and forwards to the client's function pointer; the context is unused here
   beyond showing that it is threaded all the way down. */

BOOLEAN _EverParseStreamHas(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE const x, size_t n) {
  (void) extra;
  return x->vtable.has(x, n);
}

BOOLEAN _EverParseStreamHasAt(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE const x, size_t off, size_t n) {
  (void) extra;
  return x->vtable.hasAt(x, off, n);
}

void _EverParseStreamReadBytes(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE const x, size_t n, uint8_t * const dst) {
  (void) extra;
  x->vtable.readBytes(x, n, dst);
  x->consumed += n;
}

void _EverParseStreamSkip(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE const x, size_t n) {
  (void) extra;
  x->vtable.skip(x, n);
  x->consumed += n;
}

size_t _EverParseStreamEmpty(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE const x) {
  (void) extra;
  size_t res = x->vtable.empty(x);
  x->consumed += res;
  return res;
}

uint64_t _EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE const x) {
  return x->consumed;
}

/* The pointer is the start of the next sz bytes, not the address past them, so
   that --api pulse agrees with the Low* backend. See the longer note in
   ../../static/src/EverParseStream.c. */
BOOLEAN _EverParseFieldPtrAfterImpl(EVERPARSE_EXTRA_T extra, uint64_t sz, uint8_t **out, EVERPARSE_INPUT_STREAM_BASE x) {
  (void) extra;
  uint8_t *p = x->vtable.peep(x, (size_t)sz);
  if (p == NULL)
    return FALSE;
  *out = p;
  return TRUE;
}

EVERPARSE_INPUT_STREAM_BASE EverParseCreate(EVERPARSE_STREAM_VTABLE vtable) {
  EVERPARSE_INPUT_STREAM_BASE res = malloc(sizeof(struct EVERPARSE_INPUT_STREAM_BASE_s));
  if (res == NULL)
    return NULL;
  res->head = NULL;
  res->consumed = 0;
  res->vtable = vtable;
  return res;
}

int EverParsePush(EVERPARSE_INPUT_STREAM_BASE const x, uint8_t * const buf, size_t const len) {
  struct es_cell * cell = malloc(sizeof(struct es_cell));
  if (cell == NULL)
    return 0;
  cell->buf = buf;
  cell->len = len;
  cell->next = x->head;
  x->head = cell;
  return 1;
}

void EverParseHandleError(EVERPARSE_EXTRA_T f, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code)
{
  f.handleError(f.errorContext, parsedSize, typename, fieldname, reason, error_code);
}

void EverParseRetreat(EVERPARSE_EXTRA_T f, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize)
{
}
