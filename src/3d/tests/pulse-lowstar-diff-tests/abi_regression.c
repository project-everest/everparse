/* Generated regression cases from the public Low* adapter contracts. */
#ifdef DF_READ
#include "TestActions1.h"
#else
#include "Point.h"
#endif
#include "observe.h"

static void require(int condition, const char *message) {
  if (!condition) {
    fprintf(stderr, "ABI regression: %s\n", message);
    exit(1);
  }
}

int main(void) {
  uint8_t input[32] = {0}, context = 0;
  EVERPARSE_ERROR_HANDLER handler = &df_error;
#ifdef DF_READ
  uint64_t (*read_validator)(uint32_t, uint64_t *, uint32_t *, uint32_t *,
                            uint8_t *, EVERPARSE_ERROR_HANDLER, uint8_t *,
                            uint64_t, uint64_t) = &TestActions1ValidateT;
  uint64_t (*action_validator)(uint32_t, uint32_t *, uint8_t *,
                              EVERPARSE_ERROR_HANDLER, uint8_t *,
                              uint64_t, uint64_t) = &TestActions1ValidateC;
  const uint64_t lengths[] = {3, 7, 11, 15};
  const uint64_t kinds[] = {2, 2, 6, 0};
  const uint64_t positions[] = {3, 7, 11, 15};
  for (unsigned i = 0; i < 4; ++i) {
    uint64_t x = 165;
    uint32_t xx = 165, y = 165;
    memset(input, 0, sizeof input);
    if (i == 2) input[3] = 1;
    char name[80]; snprintf(name, sizeof name, "nonzero-start-%u", i);
    df_begin(name, "TestActions1ValidateT");
    df_region("input", input, sizeof input);
    df_region("context", &context, sizeof context);
    uint64_t result = read_validator(0, &x, &xx, &y, &context, handler, input, lengths[i], 3);
    df_u64("out.x", x); df_u64("out.xx", xx); df_u64("out.y", y);
    df_end(result, 1);
    require(result >> 60 == kinds[i], "consuming result kind");
    require((result & UINT64_C(0x0fffffffffffffff)) == positions[i], "consuming position");
    require(x == (i ? 3 : 165), "first action update/preservation");
    require(xx == (i == 3 ? 7 : 165), "second action update/preservation");
    require(y == (i == 3 ? 11 : 165), "third action update/preservation");
  }
  for (unsigned i = 0; i < 2; ++i) {
    uint32_t accumulator = i;
    memset(input, 0, sizeof input);
    if (i) { input[3] = 1; input[9] = 1; }
    df_begin(i ? "partial-action-failure" : "action-failure", "TestActions1ValidateC");
    df_region("input", input, sizeof input);
    df_region("context", &context, sizeof context);
    uint64_t result = action_validator(8, &accumulator, &context, handler, input, 13, 3);
    df_u64("out.accumulator", accumulator); df_end(result, 1);
    require(result >> 60 == 5, "action failure kind is 5");
    require((result & UINT64_C(0x0fffffffffffffff)) == 13, "action failure consumed position");
    require(accumulator == (i ? 2 : 0), "partial accumulator update survives failure");
  }
#else
  uint64_t (*look_validator)(uint8_t *, EVERPARSE_ERROR_HANDLER, uint8_t *,
                            uint64_t, uint64_t) = &PointValidateTwoDPoint;
  const uint64_t lengths[] = {3, 7, 18, 19};
  for (unsigned i = 0; i < 4; ++i) {
    char name[80]; snprintf(name, sizeof name, "no-read-nonzero-%u", i);
    df_begin(name, "PointValidateTwoDPoint");
    df_region("input", input, sizeof input);
    df_region("context", &context, sizeof context);
    uint64_t result = look_validator(&context, handler, input, lengths[i], 3);
    df_end(result, 1);
    require(result == (i == 3 ? 19 : (UINT64_C(2) << 60) | 3), "no-read packed result");
    for (unsigned j = 0; j < sizeof input; ++j)
      require(input[j] == 0, "no-read validator preserves input");
  }
#endif
  return 0;
}
