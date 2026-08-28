#include "EverParseEndianness.h"
#include "EverParseStream.h"
#include <stdlib.h>

/* The primitives the generated code calls. Each one only keeps the position
   up to date and forwards to the client's function pointer. */

BOOLEAN EverParseStreamHas(EVERPARSE_INPUT_STREAM_BASE const x, size_t n) {
  return x->vtable.has(x, n);
}

BOOLEAN EverParseStreamHasAt(EVERPARSE_INPUT_STREAM_BASE const x, size_t off, size_t n) {
  return x->vtable.hasAt(x, off, n);
}

void EverParseStreamReadBytes(EVERPARSE_INPUT_STREAM_BASE const x, size_t n, uint8_t * const dst) {
  x->vtable.readBytes(x, n, dst);
  x->consumed += n;
}

void EverParseStreamSkip(EVERPARSE_INPUT_STREAM_BASE const x, size_t n) {
  x->vtable.skip(x, n);
  x->consumed += n;
}

size_t EverParseStreamEmpty(EVERPARSE_INPUT_STREAM_BASE const x) {
  size_t res = x->vtable.empty(x);
  x->consumed += res;
  return res;
}

size_t EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE const x) {
  return x->consumed;
}

BOOLEAN EverParseFieldPtrAfterImpl(uint64_t sz, uint8_t **out, EVERPARSE_INPUT_STREAM_BASE x) {
  uint8_t *p = x->vtable.peep(x, (size_t)sz);
  if (p == NULL)
    return FALSE;
  *out = p + (size_t)sz;
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
