#include "OutputWrapper.h"
#include "Output.h"
#include <assert.h>
#include <stdbool.h>

#ifdef TEST_LOWSTAR
typedef BOOLEAN API_BOOL;
#else
typedef bool API_BOOL;
#endif

_Static_assert(_Generic(((BOOL_RECORD *)0)->flag, API_BOOL: 1, default: 0),
               "output Bool field must use the selected public representation");

API_BOOL ReadFlag(BOOL_RECORD *record) { return record->flag; }

void OutputEverParseError(const char *type, const char *field, const char *reason) {
  (void)type; (void)field; (void)reason;
}

static BOOLEAN (*check)(API_BOOL, BOOL_RECORD *, BOOL_RECORD *, uint8_t *, uint32_t) =
    OutputCheckOutput;

int main(void) {
  static const unsigned seeds[] = {0, 1, 2, 255};
  for (unsigned i = 0; i < sizeof seeds / sizeof seeds[0]; ++i) {
    for (unsigned command = 0; command < 2; ++command) {
      for (unsigned tail = 0; tail < 2; ++tail) {
        API_BOOL expected = (API_BOOL)seeds[i];
        BOOL_RECORD cell = {(API_BOOL)seeds[i], 99};
        uint8_t input[] = {(uint8_t)command, tail ? 42 : 0};
        assert(check(expected, &cell, &cell, input, sizeof input) == (tail != 0));
        assert(cell.flag == command);
        assert(cell.marker == 99);

        cell.flag = (API_BOOL)seeds[i];
        BOOL_RECORD other = {(API_BOOL)!command, 77};
        assert(!check(expected, &cell, &other, input, sizeof input));
        assert(cell.flag == command);
        assert(cell.marker == 99);
        assert(other.flag == !command);
        assert(other.marker == 77);

        cell.flag = (API_BOOL)seeds[i];
        assert(!check((API_BOOL)!expected, &cell, &cell, input, sizeof input));
        assert(cell.flag == (API_BOOL)seeds[i]);
        assert(cell.marker == 99);
      }
    }
  }
  return 0;
}
