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
#ifdef LOWSTAR
  assert(is_error(EVERPARSE_VALIDATOR_ERROR_GENERIC) == 1);
  assert(is_success(0) == 1);
  assert(check_constraint((BOOLEAN)255, 7) == 7);
  assert(is_error(check_constraint((BOOLEAN)0, 7)) == 1);
  EVERPARSE_ERROR_FRAME frame;
  assert(sizeof(frame.filled) == sizeof(BOOLEAN));
#ifdef EXTERN
  EVERPARSE_INPUT_BUFFER buffer = EverParseMakeInputBufferWithLength(0, 7);
  assert(sizeof(buffer.has_length) == sizeof(BOOLEAN));
  assert(buffer.has_length == 1);
  assert(buffer.length == 7);
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
