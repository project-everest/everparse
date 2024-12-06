#ifndef __TEST_EXTERNALTYPEDEFS
#define __TEST_EXTERNALTYPEDEFS

#include <stdint.h>
#include <stddef.h>

// defining the out_t iterator type declared in Test.3d

typedef struct out_pair {
  uint32_t f1;
  uint32_t f2;
} OUT_PAIR;

typedef struct out_iterator {
  OUT_PAIR* current;
  size_t remainingCount;
} out_t;

#endif // __TEST_EXTERNALTYPEDEFS
