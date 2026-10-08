#include "LargeExtern.h"
#include <assert.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef REQUIRE_32BIT
_Static_assert(SIZE_MAX == UINT32_MAX, "run this regression with -m32");
#endif
_Static_assert(sizeof(uint64_t) == 8, "legacy counts must remain 64-bit");

static const uint64_t high = UINT64_C(4294967296);
static const uint64_t count = UINT64_C(4294967304);
static struct es_cell cell;
static struct EVERPARSE_INPUT_STREAM_BASE_s stream = { &cell };
static unsigned has_calls, skip_calls, empty_calls;
static uint64_t has_args[2], skip_arg;

static void reset(uint64_t remaining)
{
  /* Counter-only storage: no Read/Peep is legal and no bytes are allocated. */
  cell = (struct es_cell){ NULL, remaining, NULL };
  has_calls = skip_calls = empty_calls = 0;
  has_args[0] = has_args[1] = skip_arg = 0;
}

BOOLEAN EverParseHas(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base,
                     uint64_t n)
{
  assert(extra == 17 && base == &stream && has_calls < 2);
  has_args[has_calls++] = n;
  return n <= cell.len;
}

void EverParseSkip(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base,
                  uint64_t n)
{
  assert(extra == 17 && base == &stream && n <= cell.len);
  ++skip_calls;
  skip_arg = n;
  cell.len -= n;
}

uint64_t EverParseEmpty(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base)
{
  assert(extra == 17 && base == &stream);
  ++empty_calls;
  uint64_t remaining = cell.len;
  cell.len = 0;
  return remaining;
}

uint8_t *EverParseRead(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base,
                      uint64_t n, uint8_t *dst)
{
  (void)extra;
  (void)base;
  (void)n;
  (void)dst;
  fputs("unexpected Read in counter-only fixture\n", stderr);
  abort();
}

uint8_t *EverParsePeep(EVERPARSE_EXTRA_T extra, EVERPARSE_INPUT_STREAM_BASE base,
                      uint64_t n)
{
  (void)extra;
  (void)base;
  (void)n;
  fputs("unexpected Peep in counter-only fixture\n", stderr);
  abort();
}

static void run(uint64_t start)
{
  uint8_t ctxt = 0;
  EVERPARSE_INPUT_BUFFER input = EverParseMakeInputBuffer(&stream);
  uint64_t error = (UINT64_C(2) << 60) | start;

  reset(count + 32);
  assert(LargeExternNoRead(17, &ctxt, input, start) == start + count);
  assert(cell.len == count + 32 && has_calls == 2);
  assert(has_args[0] == high && has_args[1] == count);
  assert(skip_calls == 0 && empty_calls == 0);

  reset(count - 1);
  assert(LargeExternNoRead(17, &ctxt, input, start) == error);
  assert(cell.len == count - 1 && has_calls == 2);
  assert(has_args[0] == high && has_args[1] == count);
  assert(skip_calls == 0 && empty_calls == 0);

  reset(high - 1);
  assert(LargeExternNoRead(17, &ctxt, input, start) == error);
  assert(cell.len == high - 1 && has_calls == 1 && has_args[0] == high);
  assert(skip_calls == 0 && empty_calls == 0);

  reset(count + 32);
  assert(LargeExternSkip(17, &ctxt, input, start) == start + count);
  assert(cell.len == 32 && has_calls == 2);
  assert(has_args[0] == high && has_args[1] == count);
  assert(skip_calls == 1 && skip_arg == count && empty_calls == 0);

  reset(count - 1);
  assert(LargeExternSkip(17, &ctxt, input, start) == error);
  assert(cell.len == count - 1 && has_calls == 2);
  assert(skip_calls == 0 && empty_calls == 0);

  uint64_t whole = (UINT64_C(1) << 33) + 27;
  reset(whole);
  assert(LargeExternDrain(17, &ctxt, input, start) == start + whole);
  assert(cell.len == 0 && empty_calls == 1 && skip_calls == 0 && has_calls == 0);

  input = EverParseMakeInputBufferWithLength(&stream, start + count);
  reset(count + 32);
  assert(LargeExternDrain(17, &ctxt, input, start) == start + count);
  assert(cell.len == 32 && skip_calls == 1 && skip_arg == count);
  assert(empty_calls == 0 && has_calls == 0);

  reset(count + 32);
  assert(LargeExternNoRead(17, &ctxt, input, start) == start + count);
  assert(cell.len == count + 32 && has_calls == 0);
  assert(skip_calls == 0 && empty_calls == 0);
  assert(ctxt == 0);
}

int main(void)
{
  run(17);
  run((UINT64_C(1) << 40) + 17);
  printf("large extern: 16 cases passed (%zu-bit size_t, no byte storage)\n",
         8 * sizeof(size_t));
  return 0;
}
