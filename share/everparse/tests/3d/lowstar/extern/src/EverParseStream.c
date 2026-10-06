#include "EverParseEndianness.h"
#include "EverParseStream.h"
#include <stdlib.h>

BOOLEAN EverParseHas(EVERPARSE_EXTRA_T const _unused,  EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n) {
  if (n == 0)
    return TRUE;
  struct es_cell *head = x->head;
  while (head != NULL) {
    uint64_t len = head->len;
    if (n <= len)
      return TRUE;
    n -= len;
    head = head->next;
  }
  return FALSE;
}

uint8_t *EverParseRead(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n, uint8_t * const dst) {
  /** assumes EverParseHas n */
  if (n == 0)
    return dst;
  struct es_cell *head = x->head;
  uint64_t len = head->len;
  if (n <= len) {
    uint8_t *res = head->buf;
    head->buf += n;
    head->len -= n;
    return res;
  }
  uint8_t *write = dst;
  while (n > len) {
    memcpy(write, head->buf, len);
    write += len;
    n -= len;
    head = head->next;
    if (head == NULL) {
      /* here we know that n == 0 */
      x->head = NULL;
      return dst;
    }
    len = head->len;
  }
  memcpy(write, head->buf, n);
  head->buf += n;
  head->len -= n;
  x->head = head;
  return dst;
}

void EverParseSkip(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x, uint64_t n) {
  /** assumes EverParseHas n */
  if (n == 0)
    return;
  {
    struct es_cell *head = x->head;
    uint64_t len = head->len;
    while (n > len) {
      n -= len;
      head = head->next;
      if (head == NULL) {
	/* here we know that n == 0 */
	x->head = NULL;
	return;
      }
      len = head->len;
    }
    head->buf += n;
    head->len -= n;
    x->head = head;
    return;
  }
}

uint64_t EverParseEmpty(EVERPARSE_EXTRA_T const _unused, EVERPARSE_INPUT_STREAM_BASE const x) {
  uint64_t res = 0;
  struct es_cell *head = x->head;
  while (head != NULL) {
    res += head->len;
    head = head->next;
  }
  x->head = NULL;
  return res;
}

EVERPARSE_INPUT_STREAM_BASE EverParseCreate() {
  EVERPARSE_INPUT_STREAM_BASE res = malloc(sizeof(struct EVERPARSE_INPUT_STREAM_BASE_s));
  if (res == NULL) {
    return NULL;
  }
  res->head = NULL;
  return res;
}

int EverParsePush(EVERPARSE_INPUT_STREAM_BASE const x, uint8_t * const buf, uint64_t const len) {
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
