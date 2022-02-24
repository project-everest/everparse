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

// This function is declared in the generated TestWrapper.c, but not
// defined. It is the callback function called if the validator for
// Test.T fails.
void TestEverParseError(char *StructName, char *FieldName, char *Reason) {
  printf("Validation failed in Test, struct %s, field %s. Reason: %s\n", StructName, FieldName, Reason);
}

#define testSize 18

int main(void) {
  uint8_t *test = calloc(testSize, sizeof(uint8_t));
  if (test != NULL) {
    EverParseInputStreamBase testStream = EverParseCreate();
    if (testStream != NULL) {
      EverParsePush(testStream, test, testSize);
      EverParsePush(testStream, test, testSize);
      EverParsePush(testStream, test, testSize);
      if (TestCheckPoint(&_EverParseHas, &_EverParseRead, &_EverParseSkip, &_EverParseEmpty, testStream)) {
        printf("Validation succeeded\n");
      }
      free(testStream);
    }
    free(test);
  }
  return 0;
}
