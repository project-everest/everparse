#include "ExternProbe.h"
#include "ExternProbe_ExternalAPI.h"
#include <assert.h>
#include <stdio.h>

typedef struct {
  EVERPARSE_INPUT_BUFFER view;
  EVERPARSE_INPUT_BUFFER selected;
  BOOLEAN init_ok;
  BOOLEAN probe_ok;
  unsigned inits;
  unsigned probes;
} copy_buffer;

static unsigned errors;
static uint64_t first_kind, first_position;
static EVERPARSE_INPUT_BUFFER first_input;

EVERPARSE_INPUT_BUFFER EverParseStreamOf(EVERPARSE_COPY_BUFFER_T dest)
{
  copy_buffer *cb = dest;
  return cb->view;
}

BOOLEAN ProbeInit(const char *name, uint64_t len, EVERPARSE_COPY_BUFFER_T dest)
{
  copy_buffer *cb = dest;
  assert(name && len == 4);
  ++cb->inits;
  return cb->init_ok;
}

BOOLEAN ProbeInPlace(uint64_t len, uint64_t ro, uint64_t wo, uint64_t src,
                     EVERPARSE_COPY_BUFFER_T dest)
{
  copy_buffer *cb = dest;
  assert(len == 4 && ro == 0 && wo == 0 && src == 0x1234);
  ++cb->probes;
  if (!cb->probe_ok) return FALSE;
  cb->view = cb->selected;
  return TRUE;
}

static void handler(const char *type, const char *field, const char *reason,
                    uint64_t kind, uint8_t *ctxt, EVERPARSE_INPUT_BUFFER input,
                    uint64_t position)
{
  assert(type && field && reason && ctxt);
  if (errors++ == 0) {
    first_kind = kind;
    first_position = position;
    first_input = input;
  }
}

static uint64_t remaining(EVERPARSE_INPUT_STREAM_BASE stream)
{
  uint64_t n = 0;
  for (struct es_cell *cell = stream->head; cell; cell = cell->next)
    n += cell->len;
  return n;
}

static void run(unsigned split, BOOLEAN bounded, uint8_t x, uint8_t y,
                BOOLEAN init_ok, BOOLEAN probe_ok)
{
  uint8_t secondary[4] = {x, 0, y, 0};
  uint8_t primary[24] = {1, 0, 0, 0, 0, 0, 0, 0, 0x34, 0x12};
  uint8_t ctxt = 0;
  struct es_cell second = {secondary + split, sizeof secondary - split, NULL};
  struct es_cell first = {secondary, split, &second};
  struct EVERPARSE_INPUT_STREAM_BASE_s secondary_stream = {&first};
  struct EVERPARSE_INPUT_STREAM_BASE_s empty_stream = {NULL};
  struct es_cell input_cell = {primary, sizeof primary, NULL};
  struct EVERPARSE_INPUT_STREAM_BASE_s input_stream = {&input_cell};
  copy_buffer dest = {
    EverParseMakeInputBuffer(&empty_stream),
    bounded ? EverParseMakeInputBufferWithLength(&secondary_stream, 4)
            : EverParseMakeInputBuffer(&secondary_stream),
    init_ok, probe_ok, 0, 0
  };
  uint64_t start = (UINT64_C(1) << 40) + 17;
  EVERPARSE_INPUT_BUFFER input = EverParseMakeInputBuffer(&input_stream);
  errors = 0;
  uint64_t result = ExternProbeValidatePrimary(&dest, 17, &ctxt, handler, input, start);
  BOOLEAN success = init_ok && probe_ok && x >= 1 && y >= x;
  assert(result == ((success ? UINT64_C(0) : UINT64_C(5) << 60) | (start + 16)));
  assert(remaining(&input_stream) == 8 && ctxt == 0);
  assert(dest.inits == 1 && dest.probes == (unsigned)init_ok);
  assert(success ? errors == 0 : errors > 0);
  if (init_ok && probe_ok) {
    /* Consuming failures must retain the actual suffix, never rewind it. */
    assert(dest.view.base == &secondary_stream);
    assert(remaining(&secondary_stream) == (x < 1 ? 2 : 0));
    if (!success) {
      assert(first_kind == 6 && first_position == (x < 1 ? 0 : 2));
      assert(first_input.base == &secondary_stream);
      assert(first_input.has_length == bounded);
    }
  } else {
    assert(dest.view.base == &empty_stream);
    assert(remaining(&secondary_stream) == 4);
  }
}

int main(void)
{
  run(4, FALSE, 1, 2, TRUE, TRUE);
  run(1, FALSE, 1, 2, TRUE, TRUE);
  run(1, TRUE, 1, 2, TRUE, TRUE);
  run(1, TRUE, 0, 2, TRUE, TRUE);
  run(1, FALSE, 2, 1, TRUE, TRUE);
  run(4, FALSE, 1, 2, FALSE, TRUE);
  run(4, FALSE, 1, 2, TRUE, FALSE);
  puts("extern probe: scoped zero cursor, raw projection, suffixes and failures passed");
}
