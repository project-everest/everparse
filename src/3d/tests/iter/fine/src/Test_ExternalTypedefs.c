#include "Test_ExternalTypedefs.h"
#include <stdbool.h>

// defining iterator operations declared in Test.3d

static bool isOutFailure (OUT* p, uint8_t *perr) {
  *perr = 0;
  if (p == NULL)
    *perr = 1;
  if (p->remainingCount == 0)
    *perr = 1;
  return (! (*perr == 0));
}

#define CHECK_OUT(p, perr) if (isOutFailure(p, perr)) return;

void SetCurrentf1 (OUT* p, uint32_t f1, uint8_t *perr) {
  CHECK_OUT(p, perr);
  p->current->f1 = f1;
}

void SetCurrentf2 (OUT* p, uint32_t f2, uint8_t *perr) {
  CHECK_OUT(p, perr);
  p->current->f2 = f2;
}

void Advance (OUT* p, uint8_t *perr) {
  CHECK_OUT(p, perr);
  p->current++;
  p->remainingCount--;
}
