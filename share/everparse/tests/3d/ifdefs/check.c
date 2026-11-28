#include "AnonNestedStructIfDefs.h"
#include "CompileTimeIf.h"

static void error_handler(
  const char *type, const char *field, const char *reason, uint8_t code,
  uint8_t *context, uint8_t *input, size_t length, size_t *position,
  uint64_t start)
{
  (void)type;
  (void)field;
  (void)reason;
  (void)code;
  (void)context;
  (void)input;
  (void)length;
  (void)position;
  (void)start;
}

int main(void)
{
  uint8_t input[16] = {0};
  size_t position = 0;
  size_t expected = 8;
#if defined(DIM3) || defined(DIM4)
  expected += 4;
#endif
#if defined(DIM4)
  expected += 4;
#endif
  if (AnonNestedStructIfDefsValidateStaticConditionalPoint(
        NULL, error_handler, input, sizeof(input), &position) != 0 ||
      position != expected)
    return 1;

  position = 0;
  expected = 8;
#if defined(DIM3)
  expected += 4;
#elif defined(DIM4)
  expected += 8;
#endif
  if (AnonNestedStructIfDefsValidateStaticConditionalPointAlt(
        NULL, error_handler, input, sizeof(input), &position) != 0 ||
      position != expected)
    return 2;

  position = 0;
  expected = 8;
#if !(defined(DIM3) || defined(DIM4))
  expected += 4;
#endif
  if (AnonNestedStructIfDefsValidateNegatedConditionalPoint(
        NULL, error_handler, input, sizeof(input), &position) != 0 ||
      position != expected)
    return 3;

  for (uint8_t y = 1; y <= 3; ++y) {
    input[0] = 2;
    input[4] = y;
    position = 0;
    int valid = 1;
#if defined(ABOVE_DIAGONAL) && defined(STRICT)
    valid = 2 < y;
#elif defined(ABOVE_DIAGONAL)
    valid = 2 <= y;
#endif
    uint8_t result = CompileTimeIfValidatePointConditional(
      NULL, error_handler, input, 8, &position);
    if ((result == 0) != valid || (valid && position != 8))
      return 4;
  }
  return 0;
}
