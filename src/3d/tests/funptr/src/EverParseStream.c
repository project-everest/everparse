#include "EverParseStream.h"
#include <stdlib.h>

EverParseInputStreamBase EverParseCreate() {
  EverParseInputStreamBase res = malloc(sizeof(struct EverParseInputStreamBase_s));
  if (res == NULL) {
    return NULL;
  }
  res->head = NULL;
  return res;
}

int EverParsePush(EverParseInputStreamBase const x, uint8_t * const buf, uint64_t const len) {
  struct es_cell * cell = malloc(sizeof(struct es_cell));
  if (cell == NULL)
    return 0;
  cell->buf = buf;
  cell->len = len;
  cell->next = x->head;
  x->head = cell;
  return 1;
}
