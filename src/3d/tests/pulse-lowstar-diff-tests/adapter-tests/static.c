#include "Test.h"
#include <assert.h>
#include <stdio.h>

static unsigned errors, peeps;
static uint64_t callback_kind, callback_position;

static void handler(const char *type, const char *field, const char *reason,
                    uint64_t kind, uint8_t *ctxt, EVERPARSE_INPUT_BUFFER input,
                    uint64_t position)
{
  assert(type && field && reason && ctxt && input.base);
  ++errors;
  callback_kind = kind;
  callback_position = position;
}

uint8_t *__real__EverParsePeep(EVERPARSE_EXTRA_T, EVERPARSE_INPUT_STREAM_BASE, uint64_t);
uint8_t *__wrap__EverParsePeep(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE b, uint64_t n)
{
  ++peeps;
  return __real__EverParsePeep(extra, b, n);
}

static void run(unsigned split, uint64_t visible, uint64_t start)
{
  uint8_t bytes[64] = {0}, ctxt = 0;
  uint8_t *out = bytes + 63;
  struct es_cell second = {bytes + split, sizeof bytes - split, NULL};
  struct es_cell first = {bytes, split, &second};
  struct EVERPARSE_INPUT_STREAM_BASE_s stream = {&first};
  EVERPARSE_INPUT_BUFFER input = EverParseMakeInputBufferWithLength(&stream, start + visible);
  unsigned before_peeps = peeps, before_errors = errors;
  uint64_t result = TestValidatePoint(&out, 17, &ctxt, handler, input, start);
  BOOLEAN success = visible >= 26 && split >= 26;
  assert(result == (success ? start + 12 : (UINT64_C(5) << 60) + start + 8));
  assert(first.len + second.len == sizeof bytes - (success ? 12 : 8));
  assert(out == bytes + (success ? 8 : 63));
  assert(peeps - before_peeps == (visible >= 26));
  assert(errors - before_errors == !success);
  if (!success) {
    assert(callback_kind == 5 && callback_position == start + 4);
  }
}

int main(void)
{
  run(64, 64, 0);
  run(64, 64, 7);
  run(10, 64, 7);
  run(64, 12, 7);
  puts("static: Peep success/null/bounds, unchanged destination and non-consumption passed");
}
