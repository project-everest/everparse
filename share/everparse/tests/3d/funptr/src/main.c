#include "EverParseStream.h"
#include "TestWrapper.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* The client's stream operations. These are exactly what the Low* version of
   this test provides; only the types of the byte counts change, and the
   position bookkeeping now belongs to the wrappers in EverParseStream.c. */

/* Number of bytes still available, capped at `limit`. */
static size_t _EverParseAvail(EVERPARSE_INPUT_STREAM_BASE const x, size_t const limit) {
  size_t got = 0;
  struct es_cell *head = x->head;
  while (head != NULL && got < limit) {
    got += head->len;
    head = head->next;
  }
  return got;
}

static BOOLEAN _EverParseHas(EVERPARSE_INPUT_STREAM_BASE x, size_t n) {
  return _EverParseAvail(x, n) >= n ? TRUE : FALSE;
}

static BOOLEAN _EverParseHasAt(EVERPARSE_INPUT_STREAM_BASE x, size_t off, size_t n) {
  size_t total = off + n;
  if (total < off)
    return FALSE; /* overflow */
  return _EverParseAvail(x, total) >= total ? TRUE : FALSE;
}

/* Drop the first n bytes, copying them to dst first when dst is not NULL.
   Assumes they are available. */
static void _EverParseConsume(EVERPARSE_INPUT_STREAM_BASE const x, size_t n, uint8_t *dst) {
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

static void _EverParseReadBytes(EVERPARSE_INPUT_STREAM_BASE x, size_t n, uint8_t *dst) {
  _EverParseConsume(x, n, dst);
}

static void _EverParseSkip(EVERPARSE_INPUT_STREAM_BASE x, size_t n) {
  _EverParseConsume(x, n, NULL);
}

static size_t _EverParseEmpty(EVERPARSE_INPUT_STREAM_BASE x) {
  size_t res = 0;
  struct es_cell *head = x->head;
  while (head != NULL) {
    res += head->len;
    head = head->next;
  }
  x->head = NULL;
  return res;
}

static uint8_t *_EverParsePeep(EVERPARSE_INPUT_STREAM_BASE x, size_t n) {
  struct es_cell *head = x->head;
  while (head != NULL && head->len == 0)
    head = head->next;
  if (head == NULL)
    return n == 0 ? (uint8_t *)x : NULL;
  if (head->len < n)
    return NULL;
  return head->buf;
}

static EVERPARSE_STREAM_VTABLE makeVTable(void) {
  EVERPARSE_STREAM_VTABLE out = {
      .has = &_EverParseHas,
      .hasAt = &_EverParseHasAt,
      .readBytes = &_EverParseReadBytes,
      .skip = &_EverParseSkip,
      .empty = &_EverParseEmpty,
      .peep = &_EverParsePeep
  };
  return out;
}

// The callback called if the validator for Test.T fails.
static void _EverParseError(void *status, uint64_t position, const char *StructName, const char *FieldName, const char *Reason, uint64_t error_code) {
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
  *((BOOLEAN*)status) = FALSE;
}

static EVERPARSE_EXTRA_T makeExtraT(void *ctx) {
  EVERPARSE_EXTRA_T out = {
      .errorContext = ctx,
      .handleError = &_EverParseError
  };
  return out;
}

int test(uint32_t chunkSize, uint32_t numChunks) {
  uint8_t *chunk = calloc(chunkSize, sizeof(uint8_t));
  EVERPARSE_INPUT_STREAM_BASE testStream = EverParseCreate(makeVTable());
  BOOLEAN status = TRUE;
  uint32_t i = numChunks;
  if (chunk != NULL) {
    if (testStream != NULL) {
      while (i-- > 0) {
        EverParsePush(testStream, chunk, (size_t)chunkSize);
      }
      EVERPARSE_EXTRA_T ex = makeExtraT(&status);
      TestCheckPoint(ex, testStream);
      if (status) {
        printf("Validation succeeded (chunk_size=%u, n_chunks=%u), read %zu bytes\n", chunkSize, numChunks, EverParseStreamGetPosition(testStream));
      }
      else {
        printf("Validation failed (chunk_size=%u, n_chunks=%u), read %zu bytes\n", chunkSize, numChunks, EverParseStreamGetPosition(testStream));
      }
      free(testStream);
    }
    free(chunk);
  }
  return status;
}

int main(void) {
  if (!test(2, 6)) { return 1; }
  if (!test(3, 9)) { return 1; }
  if (test(3, 3))  { return 1; }
  if (test(2, 5))  { return 1; }
  return 0;
}
