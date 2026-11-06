#include "MutableWrapper.h"
#include "Mutable.h"
#include <assert.h>
#include <stdbool.h>

#ifdef TEST_LOWSTAR
typedef BOOLEAN API_BOOL;
#else
typedef bool API_BOOL;
#endif

API_BOOL IsSet(uint8_t value) {
#ifdef TEST_LOWSTAR
  return value ? 0xff : 0;
#else
  return value != 0;
#endif
}

void MutableEverParseError(const char *type, const char *field, const char *reason) {
  (void)type; (void)field; (void)reason;
}

static BOOLEAN (*check)(API_BOOL, API_BOOL *, API_BOOL *, uint8_t *, uint32_t) =
    MutableCheckMutable;

int main(void) {
  static const unsigned seeds[] = {0, 1, 2, 255};
  for (unsigned i = 0; i < sizeof seeds / sizeof seeds[0]; ++i) {
    for (unsigned command = 0; command < 2; ++command) {
      for (unsigned tail = 0; tail < 2; ++tail) {
        API_BOOL cell = (API_BOOL)seeds[i];
        API_BOOL expected = (API_BOOL)seeds[i];
        uint8_t input[] = {(uint8_t)command, tail ? 42 : 0};
        assert(check(expected, &cell, &cell, input, sizeof input) == (tail != 0));
        /* Writes are canonical even when validation fails after the action. */
        assert(cell == command);

        cell = (API_BOOL)seeds[i];
        API_BOOL other = (API_BOOL)!command;
        assert(!check(expected, &cell, &other, input, sizeof input));
        assert(cell == command);
        assert(other == !command);

        /* A rejected read must not normalize the caller's byte in place. */
        cell = (API_BOOL)seeds[i];
        assert(!check((API_BOOL)!expected, &cell, &cell, input, sizeof input));
        assert(cell == (API_BOOL)seeds[i]);
      }
    }
  }
  return 0;
}
