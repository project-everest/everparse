#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifdef TEST_EXTERN
typedef void *EVERPARSE_INPUT_STREAM_BASE;
typedef void *EVERPARSE_EXTRA_T;
#endif
#include "EverParse.h"

#ifdef TEST_STATIC
static inline BOOLEAN EverParseHas(EVERPARSE_EXTRA_T x, EVERPARSE_INPUT_STREAM_BASE b, uint64_t n)
{ (void)x; (void)b; return n == 0; }
static inline void EverParseSkip(EVERPARSE_EXTRA_T x, EVERPARSE_INPUT_STREAM_BASE b, uint64_t n)
{ (void)x; (void)b; (void)n; }
static inline uint64_t EverParseEmpty(EVERPARSE_EXTRA_T x, EVERPARSE_INPUT_STREAM_BASE b)
{ (void)x; (void)b; return 0; }
static uint8_t *EverParseRead(EVERPARSE_EXTRA_T x, EVERPARSE_INPUT_STREAM_BASE b, uint64_t n, uint8_t *dst)
{ (void)x; (void)b; (void)n; return dst; }
static uint8_t *EverParsePeep(EVERPARSE_EXTRA_T x, EVERPARSE_INPUT_STREAM_BASE b, uint64_t n)
{ (void)x; (void)n; return (uint8_t *)b; }
#endif

static void callback(PRIMS_STRING t, PRIMS_STRING f, PRIMS_STRING r, uint64_t e,
                     EVERPARSE_APP_CTXT c, EVERPARSE_INPUT_BUFFER input, uint64_t p)
{ (void)t; (void)f; (void)r; (void)e; (void)c; (void)input; (void)p; }

int main(void)
{
  const uint64_t mask = (UINT64_C(1) << 60) - 1;
  const uint64_t positions[] = {0, 1, UINT32_MAX, UINT64_C(1) << 32, mask - 1, mask};
  const uint64_t errors[] = {
    EVERPARSE_VALIDATOR_ERROR_GENERIC, EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
    EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE, EVERPARSE_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE,
    EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED, EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED,
    EVERPARSE_VALIDATOR_ERROR_UNEXPECTED_PADDING, EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED
  };
  const char *reasons[] = {
    "unspecified", "generic error", "not enough data", "impossible",
    "list size not multiple of element size", "action failed", "constraint failed",
    "unexpected padding", "probe failed"
  };
  assert(EVERPARSE_VALIDATOR_MAX_LENGTH == mask);
  for (size_t k = 0; k < sizeof(errors) / sizeof(errors[0]); ++k)
    assert(errors[k] == (uint64_t)(k + 1) << 60);
  for (uint64_t k = 0; k < 16; ++k) {
    for (size_t i = 0; i < sizeof(positions) / sizeof(positions[0]); ++i) {
      uint64_t p = positions[i], packed = (k << 60) | p;
      assert(EverParseGetValidatorErrorKind(packed) == k);
      assert(EverParseGetValidatorErrorPos(packed) == p);
      assert(EverParseSetValidatorErrorKind(UINT64_MAX - mask + p, k) == packed);
      assert(EverParseSetValidatorErrorPos((k << 60) | mask, p) == packed);
      assert(EverParseIsSuccess(packed) == (k == 0));
      assert(EverParseIsError(packed) == (k != 0));
      assert(strcmp(EverParseErrorReasonOfResult(packed), k < 9 ? reasons[k] : "unspecified") == 0);
      assert(EverParseCheckConstraintOk(TRUE, p) == p);
      assert(EverParseCheckConstraintOk(FALSE, p) == ((UINT64_C(6) << 60) | p));
    }
  }
  const uint32_t bounds[] = {0, 1, 7, UINT32_MAX - 1, UINT32_MAX};
  for (size_t s = 0; s < 5; ++s)
    for (size_t o = 0; o < 5; ++o)
      for (size_t a = 0; a < 5; ++a)
        assert(EverParseIsRangeOkay(bounds[s], bounds[o], bounds[a]) ==
               ((uint64_t)bounds[o] + bounds[a] <= bounds[s]));
#define CHECK_BITS(width, type) do { \
    type value = (type)UINT64_C(0x96a53cf087c25bd1); \
    for (uint32_t from = 0; from < width; ++from) \
      for (uint32_t to = from + 1; to <= width; ++to) { \
        uint64_t m = UINT64_MAX >> (64 - (to - from)); \
        assert(EverParseGetBitfield##width(value, from, to) == (((uint64_t)value >> from) & m)); \
        assert(EverParseGetBitfield##width##MsbFirst(value, from, to) == \
               (((uint64_t)value >> (width - to)) & m)); \
      } \
  } while (0)
  CHECK_BITS(8, uint8_t);
  CHECK_BITS(16, uint16_t);
  CHECK_BITS(32, uint32_t);
  CHECK_BITS(64, uint64_t);

  uint8_t bytes[1] = {0};
#ifdef TEST_EXTERN
  EVERPARSE_INPUT_BUFFER input = EverParseMakeInputBuffer(bytes);
  assert(input.base == bytes && !input.has_length && input.length == 0);
  input = EverParseMakeInputBufferWithLength(bytes, UINT64_MAX);
  assert(input.base == bytes && input.has_length && input.length == UINT64_MAX);
  printf("%zu %zu %zu %zu\n", sizeof(input), offsetof(EVERPARSE_INPUT_BUFFER, base),
         offsetof(EVERPARSE_INPUT_BUFFER, has_length), offsetof(EVERPARSE_INPUT_BUFFER, length));
#else
  EVERPARSE_INPUT_BUFFER input = bytes;
  printf("%zu\n", sizeof(input));
#endif
  EVERPARSE_ERROR_HANDLER handler = callback;
  handler("type", "field", "reason", errors[5], bytes, input, mask);
  EVERPARSE_ERROR_FRAME frame;
  memset(&frame, 0, sizeof(frame));
  for (unsigned int call = 0; call < 2; ++call) {
    EverParseDefaultErrorHandler(call ? "other" : "type", call ? "other" : "field",
                                call ? "other" : "reason", call ? 0 : errors[5],
                                &frame, input, call ? 0 : mask);
    assert(frame.filled && frame.start_pos == mask && frame.error_code == errors[5]);
    assert(strcmp(frame.typename_s, "type") == 0);
    assert(strcmp(frame.fieldname, "field") == 0);
    assert(strcmp(frame.reason, "reason") == 0);
  }
  printf("%zu %zu %zu %zu %zu %zu %zu\n", sizeof(frame),
         offsetof(EVERPARSE_ERROR_FRAME, filled), offsetof(EVERPARSE_ERROR_FRAME, start_pos),
         offsetof(EVERPARSE_ERROR_FRAME, typename_s), offsetof(EVERPARSE_ERROR_FRAME, fieldname),
         offsetof(EVERPARSE_ERROR_FRAME, reason), offsetof(EVERPARSE_ERROR_FRAME, error_code));
#ifdef TEST_LOWSTAR
  const uint8_t statuses[] = {
    EVERPARSEPULSEINTERNAL_VALIDATOR_SUCCESS, EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
    EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_IMPOSSIBLE, EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE,
    EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_ACTION_FAILED, EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_CONSTRAINT_FAILED,
    EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_UNEXPECTED_PADDING, EVERPARSEPULSEINTERNAL_VALIDATOR_ERROR_PROBE_FAILED
  };
  for (size_t i = 0; i < sizeof(statuses); ++i)
    assert(statuses[i] == (i == 0 ? 0 : i + 1));
  for (unsigned int k = 0; k <= UINT8_MAX; ++k) {
    const char *reason = k == 0 ? "success" : k >= 2 && k <= 8 ? reasons[k] : "unspecified";
    assert(strcmp(EverParsePulseInternalErrorReasonOfResult((uint8_t)k), reason) == 0);
  }
  assert(EverParsePulseInternalIsRangeOkay(UINT32_MAX, UINT32_MAX, 0));
  assert(!EverParsePulseInternalIsRangeOkay(UINT32_MAX, UINT32_MAX, 1));
#endif
  return 0;
}
