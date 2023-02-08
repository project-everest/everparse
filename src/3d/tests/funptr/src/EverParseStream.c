#include "EverParseStream.h"
#include <stdlib.h>

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
