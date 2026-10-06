#include "Test.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

static unsigned errors, reads, skips, direct_reads, scratch_reads;
static uint64_t callback_kind, callback_position;
static EVERPARSE_INPUT_BUFFER callback_input;

static void handler(const char *type, const char *field, const char *reason,
                    uint64_t kind, uint8_t *ctxt, EVERPARSE_INPUT_BUFFER input,
                    uint64_t position)
{
  assert(type && field && reason && ctxt);
  if (errors == 0) {
    callback_kind = kind;
    callback_position = position;
    callback_input = input;
  }
  ++errors;
}

uint8_t *__real_EverParseRead(EVERPARSE_EXTRA_T, EVERPARSE_INPUT_STREAM_BASE,
                            uint64_t, uint8_t *);
void __real_EverParseSkip(EVERPARSE_EXTRA_T, EVERPARSE_INPUT_STREAM_BASE, uint64_t);

uint8_t *__wrap_EverParseRead(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE b,
                            uint64_t n, uint8_t *dst)
{
  ++reads;
  uint8_t *result = __real_EverParseRead(extra, b, n, dst);
  if (result == dst) ++scratch_reads; else ++direct_reads;
  return result;
}

void __wrap_EverParseSkip(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE b,
                         uint64_t n)
{
  ++skips;
  __real_EverParseSkip(extra, b, n);
}

static void run(unsigned split, uint32_t y, uint64_t start, uint64_t visible)
{
  uint8_t bytes[32] = {0}, ctxt = 0;
  /* Test.3d is little-endian independently of the host ABI. */
  for (unsigned i = 0; i < 4; ++i) bytes[4 + i] = (uint8_t)(y >> (8 * i));
  struct es_cell second = {bytes + split, sizeof bytes - split, NULL};
  struct es_cell first = {bytes, split, &second};
  struct EVERPARSE_INPUT_STREAM_BASE_s stream = {&first};
  EVERPARSE_INPUT_BUFFER input = EverParseMakeInputBufferWithLength(&stream, start + visible);
  errors = 0;
  unsigned before_reads = reads, before_skips = skips;
  uint64_t result = TestValidatePoint(17, &ctxt, handler, input, start);
  uint64_t consumed = visible < 4 ? 0 : visible < 8 ? 4 : y < 18 ? 8 : visible < 12 ? 8 : 12;
  uint64_t kind = visible < 8 ? 2 : y < 18 ? 6 : visible < 12 ? 2 : 0;
  assert(result == (kind << 60) + start + consumed);
  uint64_t remaining = 0;
  for (struct es_cell *cell = stream.head; cell; cell = cell->next) remaining += cell->len;
  assert(remaining == sizeof bytes - consumed);
  assert(reads - before_reads == (consumed >= 8 ? 1u : 0u));
  assert(skips - before_skips == (consumed == 12 ? 2u : consumed >= 4 ? 1u : 0u));
  assert(kind != 0 ? errors > 0 : errors == 0);
  if (kind != 0) {
    assert(callback_kind == kind);
    assert(callback_position == start + (visible < 4 ? 0 : visible < 8 || y < 18 ? 4 : 8));
    assert(callback_input.base == &stream && callback_input.has_length);
    assert(callback_input.length == start + visible);
  }
}

int main(void)
{
  run(32, 18, 0, 32);
  run(6, 18, 7, 32);
  run(6, 17, 7, 32);
  run(32, 18, 7, 3);
  run(32, 18, 7, 6);
  run(32, 18, 7, 10);
  run(32, 18, (UINT64_C(1) << 40), 12);
  assert(direct_reads > 0 && scratch_reads > 0);
  puts("extern: packed positions, callback ABI, suffixes, direct/scratch Read passed");
}
