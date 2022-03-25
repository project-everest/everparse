#include "EverParseStream.h"
#include "TestWrapper.h"
#include <stdio.h>
#include <stdlib.h>

static BOOLEAN _EverParseHas(EverParseInputStreamBase const x, uint64_t n) {
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

static uint8_t *_EverParseRead(EverParseInputStreamBase const x, uint64_t n, uint8_t * const dst) {
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

static void _EverParseSkip(EverParseInputStreamBase const x, uint64_t n) {
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

static uint64_t _EverParseEmpty(EverParseInputStreamBase const x) {
  uint64_t res = 0;
  struct es_cell *head = x->head;
  while (head != NULL) {
    res += head->len;
    head = head->next;
  }
  x->head = NULL;
  return res;
}

void _EverParseRetreat(EverParseInputStreamBase const x, uint64_t n) {
  printf("Warning, no retreat");
}

// This function is declared in the generated TestWrapper.c, but not
// defined. It is the callback function called if the validator for
// Test.T fails.
void _EverParseError(void *status, uint64_t position, const char *StructName, const char *FieldName, const char *Reason) {
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
  *((BOOLEAN*)status) = FALSE;
}

EverParseExtraT makeExtraT(void *ctx) {
  EverParseExtraT out = {
      .has = &_EverParseHas,
      .read = &_EverParseRead,
      .skip = &_EverParseSkip,
      .empty = &_EverParseEmpty,
      .handleError = &_EverParseError,
      .retreat = &_EverParseRetreat,
      .errorContext = ctx
  };
  return out;
}


int test(uint32_t chunkSize, uint32_t numChunks) {
  uint8_t *chunk = calloc(chunkSize, sizeof(uint8_t));
  EverParseInputStreamBase testStream = EverParseCreate();
  BOOLEAN status = TRUE;
  uint32_t i = numChunks;
  if (chunk != NULL) {
    if (testStream != NULL) {
      while (i-- > 0) {
        EverParsePush(testStream, chunk, chunkSize);
      }
      EverParseExtraT ex = makeExtraT(&status);
      uint64_t bytesRead = TestCheckPoint(ex, testStream);
      if (status) {
        printf("Validation succeeded (chunk_size=%u, n_chunks=%u), read %u bytes\n", chunkSize, numChunks, bytesRead);
      }
      else {
        printf("Validation failed (chunk_size=%u, n_chunks=%u), read %u bytes\n", chunkSize, numChunks, bytesRead);
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
  
