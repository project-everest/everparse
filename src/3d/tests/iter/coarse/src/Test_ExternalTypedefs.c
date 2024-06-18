#include "Test_ExternalTypedefs.h"
#include <stdbool.h>

// defining iterator operations declared in Test.3d

static bool isOutFailure (OUT* p) {
  if (p == NULL)
    return true;
  if (p->remainingCount == 0)
    p->current = NULL;
  return (p->current == NULL);
}

#define CHECK_OUT(p) if (isOutFailure(p)) return;

void SetCurrentf1 (OUT* p, uint32_t f1) {
  CHECK_OUT(p);
  p->current->f1 = f1;
}

void SetCurrentf2 (OUT* p, uint32_t f2) {
  CHECK_OUT(p);
  p->current->f2 = f2;
}

void Advance (OUT* p) {
  CHECK_OUT(p);
  p->current++;
  p->remainingCount--;
}
