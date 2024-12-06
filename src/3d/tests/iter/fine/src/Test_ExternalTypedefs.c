#include "Test_ExternalTypedefs.h"
#include <stdbool.h>

// defining iterator operations declared in Test.3d

static uint8_t isOutFailure (out_t* p) {
  if (p == NULL)
    return 1;
  if (p->remainingCount == 0)
    return 1;
  return 0;
}

#define CHECK_OUT(p) { uint8_t err = isOutFailure(p); if (err) return err; }

uint8_t SetCurrentf1 (out_t* p, uint32_t f1) {
  CHECK_OUT(p);
  p->current->f1 = f1;
  return 0;
}

uint8_t SetCurrentf2 (out_t* p, uint32_t f2) {
  CHECK_OUT(p);
  p->current->f2 = f2;
  return 0;
}

uint8_t Advance (out_t* p) {
  CHECK_OUT(p);
  p->current++;
  p->remainingCount--;
  return 0;
}
