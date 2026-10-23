#include "ProbesWrapper.h"
#include "Probes.h"
#include <assert.h>
#include <stdbool.h>
#include <string.h>

#ifdef TEST_LOWSTAR
typedef BOOLEAN API_BOOL;
#else
typedef bool API_BOOL;
#endif

typedef struct {
  uint8_t data[16];
  size_t len;
  size_t pos;
} copy_buffer;

enum { OK, INIT_FAIL, COPY_FAIL, READ_FAIL, WRITE_FAIL };
static unsigned mode, truth;
static unsigned calls[5];

uint8_t *EverParseStreamOf(EVERPARSE_COPY_BUFFER_T cb) {
  return ((copy_buffer *)cb)->data;
}
size_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T cb) {
  return ((copy_buffer *)cb)->len;
}
size_t *EverParseStreamPos(EVERPARSE_COPY_BUFFER_T cb) {
  return &((copy_buffer *)cb)->pos;
}
uint64_t UlongToPtr(uint32_t pointer) { return pointer; }

API_BOOL ProbeInit(const char *name, uint64_t len, EVERPARSE_COPY_BUFFER_T cb) {
  (void)name;
  ++calls[INIT_FAIL];
  assert(len <= sizeof ((copy_buffer *)cb)->data);
  ((copy_buffer *)cb)->len = (size_t)len;
  return mode == INIT_FAIL ? 0 : (API_BOOL)truth;
}

API_BOOL ProbeAndCopy(uint64_t len, uint64_t ro, uint64_t wo, uint64_t src,
                     EVERPARSE_COPY_BUFFER_T cb) {
  ++calls[COPY_FAIL];
  uint64_t value = src == 1 ? 2 : 42;
  assert(ro + len <= sizeof value);
  assert(wo + len <= sizeof ((copy_buffer *)cb)->data);
  memcpy(((copy_buffer *)cb)->data + wo, (uint8_t *)&value + ro, (size_t)len);
  return mode == COPY_FAIL ? 0 : (API_BOOL)truth;
}

uint32_t ProbeAndReadU32(API_BOOL *failed, uint64_t ro, uint64_t src,
                         EVERPARSE_COPY_BUFFER_T cb) {
  (void)cb;
  ++calls[READ_FAIL];
  assert(!*failed);
  assert(ro == 0);
  if (mode == READ_FAIL) {
    *failed = (API_BOOL)truth;
    return 0;
  }
  return src == 1 ? 2 : 42;
}

API_BOOL WriteU64(uint64_t value, uint64_t wo, EVERPARSE_COPY_BUFFER_T cb) {
  ++calls[WRITE_FAIL];
  assert(wo + sizeof value <= sizeof ((copy_buffer *)cb)->data);
  memcpy(((copy_buffer *)cb)->data + wo, &value, sizeof value);
  return mode == WRITE_FAIL ? 0 : (API_BOOL)truth;
}

void ProbesEverParseError(const char *type, const char *field, const char *reason) {
  (void)type; (void)field; (void)reason;
}

int main(void) {
  const unsigned truths[] = {1, 2, 255};
  for (unsigned t = 0; t < sizeof truths / sizeof truths[0]; ++t) {
    truth = truths[t];
    for (mode = OK; mode <= WRITE_FAIL; ++mode) {
      copy_buffer a = {{0}, 0, 0}, b = {{0}, 0, 0};
      uint64_t source = 1;
      memset(calls, 0, sizeof calls);
      assert(ProbesCheckC((API_BOOL)truth, &a, &b,
                         (uint8_t *)&source, sizeof source) == (mode == OK));
      if (mode != OK)
        assert(calls[mode] != 0);
      else
        for (unsigned c = INIT_FAIL; c <= WRITE_FAIL; ++c)
          assert(calls[c] != 0);
    }
  }
  return 0;
}
