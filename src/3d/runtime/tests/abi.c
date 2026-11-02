#include <stdint.h>

typedef void *EVERPARSE_INPUT_STREAM_BASE;
typedef uintptr_t EVERPARSE_EXTRA_T;

#if defined(STATIC) && defined(HOOKS_FIRST)
#include "static-hooks.h"
#endif

#include "EverParse.h"

#if defined(STATIC) && !defined(HOOKS_FIRST)
#include "static-hooks.h"
#endif

#include <assert.h>
#include <stddef.h>
#include <string.h>

int check_types(void);

static BOOLEAN (*const range_okay)(uint32_t, uint32_t, uint32_t) =
  EverParseIsRangeOkay;

#ifdef LOWSTAR
static BOOLEAN (*const is_error)(uint64_t) = EverParseIsError;
static BOOLEAN (*const is_success)(uint64_t) = EverParseIsSuccess;
static uint64_t (*const check_constraint)(BOOLEAN, uint64_t) = EverParseCheckConstraintOk;
#endif

int main(void)
{
  assert(sizeof(BOOLEAN) == 1);
  assert(range_okay(16, 8, 8) == 1);
  assert(range_okay(16, 9, 8) == 0);
  assert(check_types() == 0);
  uint64_t value = UINT64_C(0x9876543210abcdef);
  for (uint32_t from = 0; from < 64; ++from)
  {
    for (uint32_t to = from + 1; to <= 64; ++to)
    {
      uint32_t width = to - from;
      uint64_t mask = width == 64 ? UINT64_MAX : (UINT64_C(1) << width) - 1;
      uint64_t expected = (value >> from) & mask;
      assert(EverParseGetBitfield64(value, from, to) == expected);
      assert(EverParseGetBitfield64MsbFirst(value, 64 - to, 64 - from) == expected);
      if (to <= 32)
      {
        assert(EverParseGetBitfield32((uint32_t)value, from, to) == expected);
        assert(EverParseGetBitfield32MsbFirst((uint32_t)value, 32 - to, 32 - from) == expected);
      }
      if (to <= 16)
      {
        assert(EverParseGetBitfield16((uint16_t)value, from, to) == expected);
        assert(EverParseGetBitfield16MsbFirst((uint16_t)value, 16 - to, 16 - from) == expected);
      }
      if (to <= 8)
      {
        assert(EverParseGetBitfield8((uint8_t)value, from, to) == expected);
        assert(EverParseGetBitfield8MsbFirst((uint8_t)value, 8 - to, 8 - from) == expected);
      }
    }
  }
  EVERPARSE_ERROR_FRAME frame;
  assert(sizeof(frame.filled) == sizeof(BOOLEAN));
  uint8_t *filled = &frame.filled;
  (void)filled;
  struct reference_frame {
    uint8_t filled;
    uint64_t start_pos;
    const char *typename_s;
    const char *fieldname;
    const char *reason;
    uint64_t error_code;
  };
  assert(sizeof(frame) == sizeof(struct reference_frame));
#define CHECK_FRAME_FIELD(field) \
  assert(offsetof(EVERPARSE_ERROR_FRAME, field) == offsetof(struct reference_frame, field))
  CHECK_FRAME_FIELD(filled);
  CHECK_FRAME_FIELD(start_pos);
  CHECK_FRAME_FIELD(typename_s);
  CHECK_FRAME_FIELD(fieldname);
  CHECK_FRAME_FIELD(reason);
  CHECK_FRAME_FIELD(error_code);
#undef CHECK_FRAME_FIELD
#ifdef LOWSTAR
  EVERPARSE_INPUT_BUFFER input;
  memset(&input, 0, sizeof(input));
#define FIRST_ERROR EVERPARSE_VALIDATOR_ERROR_GENERIC
#define SECOND_ERROR EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED
#else
  uint8_t *input = NULL;
#define FIRST_ERROR EVERPARSE_STATUS_ERROR_IMPOSSIBLE
#define SECOND_ERROR EVERPARSE_STATUS_ERROR_PROBE_FAILED
#endif
  memset(&frame, 0, sizeof(frame));
  EverParseDefaultErrorHandler("T", "f", "first", FIRST_ERROR,
                              &frame, input, 17);
  assert(frame.filled == 1);
  assert(frame.start_pos == 17);
  assert(frame.error_code == FIRST_ERROR);
  assert(strcmp(frame.reason, "first") == 0);
  frame.filled = (BOOLEAN)255;
  EverParseDefaultErrorHandler("U", "g", "second", SECOND_ERROR,
                              &frame, input, 99);
  assert(frame.filled == (BOOLEAN)255);
  assert(frame.start_pos == 17);
  assert(strcmp(frame.reason, "first") == 0);
#undef FIRST_ERROR
#undef SECOND_ERROR
#ifdef LOWSTAR
  assert(is_error(EVERPARSE_VALIDATOR_ERROR_GENERIC) == 1);
  assert(is_success(0) == 1);
  assert(check_constraint((BOOLEAN)255, 7) == 7);
  assert(is_error(check_constraint((BOOLEAN)0, 7)) == 1);
  for (uint64_t kind = 0; kind < 16; ++kind)
  {
    uint64_t error = EverParseSetValidatorErrorKind(0, kind);
    error = EverParseSetValidatorErrorPos(error, EVERPARSE_VALIDATOR_MAX_LENGTH);
    assert(EverParseGetValidatorErrorKind(error) == kind);
    assert(EverParseGetValidatorErrorPos(error) == EVERPARSE_VALIDATOR_MAX_LENGTH);
  }
#ifdef EXTERN
  EVERPARSE_INPUT_BUFFER buffer = EverParseMakeInputBufferWithLength(0, 7);
  assert(sizeof(buffer.has_length) == sizeof(BOOLEAN));
  assert(buffer.has_length == 1);
  assert(buffer.length == 7);
  uint8_t *has_length = &buffer.has_length;
  (void)has_length;
  struct reference_buffer {
    EVERPARSE_INPUT_STREAM_BASE base;
    uint8_t has_length;
    uint64_t length;
  };
  assert(sizeof(buffer) == sizeof(struct reference_buffer));
  assert(offsetof(EVERPARSE_INPUT_BUFFER, has_length) ==
         offsetof(struct reference_buffer, has_length));
  assert(offsetof(EVERPARSE_INPUT_BUFFER, length) ==
         offsetof(struct reference_buffer, length));
#endif
#endif
#ifdef STATIC
#ifdef LOWSTAR
  assert(EverParseHas(0, 0, 0) == (BOOLEAN)255);
#else
  assert(EverParseStreamHas(0, 0, 0) == (BOOLEAN)255);
#endif
#endif
  return 0;
}
