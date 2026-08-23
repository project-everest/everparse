#include "EverParseEndianness.h"
#include "EverParseStream.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Number of bytes still available, capped at `limit` so that a long chain is
   not walked further than the caller cares about. */
static size_t es_avail(EVERPARSE_INPUT_STREAM_BASE const x, size_t const limit) {
  size_t got = 0;
  struct es_cell *head = x->head;
  while (head != NULL && got < limit) {
    got += head->len;
    head = head->next;
  }
  return got;
}

BOOLEAN EverParseStreamHas(EVERPARSE_INPUT_STREAM_BASE const x, size_t n) {
  return es_avail(x, n) >= n ? TRUE : FALSE;
}

BOOLEAN EverParseStreamHasAt(EVERPARSE_INPUT_STREAM_BASE const x, size_t off, size_t n) {
  /** assumes off bytes are available */
  size_t total = off + n;
  if (total < off)
    return FALSE; /* overflow */
  return es_avail(x, total) >= total ? TRUE : FALSE;
}

size_t EverParseStreamGetPosition(EVERPARSE_INPUT_STREAM_BASE const x) {
  return x->consumed;
}

/* Drop the first n bytes of the stream, copying them to dst first when dst is
   not NULL. Assumes EverParseStreamHas(x, n). */
static void es_consume(EVERPARSE_INPUT_STREAM_BASE const x, size_t n, uint8_t *dst) {
  x->consumed += n;
  while (n > 0) {
    struct es_cell *head = x->head;
    size_t len, take;
    while (head->len == 0) { /* skip exhausted cells */
      head = head->next;
      x->head = head;
    }
    len = head->len;
    take = n < len ? n : len;
    if (dst != NULL) {
      memcpy(dst, head->buf, take);
      dst += take;
    }
    head->buf += take;
    head->len -= take;
    n -= take;
    if (head->len == 0)
      x->head = head->next;
  }
}

void EverParseStreamReadBytes(EVERPARSE_INPUT_STREAM_BASE const x, size_t n, uint8_t * const dst) {
  /** assumes EverParseStreamHas(x, n) */
  es_consume(x, n, dst);
}

void EverParseStreamSkip(EVERPARSE_INPUT_STREAM_BASE const x, size_t n) {
  /** assumes EverParseStreamHas(x, n) */
  es_consume(x, n, NULL);
}

size_t EverParseStreamEmpty(EVERPARSE_INPUT_STREAM_BASE const x) {
  size_t res = 0;
  struct es_cell *head = x->head;
  while (head != NULL) {
    res += head->len;
    head = head->next;
  }
  x->head = NULL;
  x->consumed += res;
  return res;
}

EVERPARSE_INPUT_STREAM_BASE EverParseCreate(void) {
  EVERPARSE_INPUT_STREAM_BASE res = malloc(sizeof(struct EVERPARSE_INPUT_STREAM_BASE_s));
  if (res == NULL) {
    return NULL;
  }
  res->head = NULL;
  res->consumed = 0;
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

void EverParseHandleError(EVERPARSE_EXTRA_T _dummy, uint64_t parsedSize, const char *typename, const char *fieldname, const char *reason, uint64_t error_code)
{
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", typename, fieldname, reason);
}

void EverParseRetreat(EVERPARSE_EXTRA_T _dummy, EVERPARSE_INPUT_STREAM_BASE base, uint64_t parsedSize)
{
}
