#include <stdint.h>
#include <iostream>
#include "TPointWrapper.h"

void TPointEverParseError(const char *StructName, const char *FieldName, const char *Reason)
{
  std::cout << "Validation failed" << std::endl;
}

using namespace std;

int main ()
{
  Otpoint s1 = { {1, 2}, 3 };
  Otpoint s2;

  TpointCheckFlattpoint (&s2, (uint8_t *) &s1, 12);
  if (s2.op.x == 1 && s2.op.y == 2 && s2.oz == 3) {
    std::cout << "Output types testcase (TPoint) success!" << std::endl;
    return 0;
  } else {
    std::cout << "Output types testcase (TPoint) err!" << std::endl;
    return 1;
  }
}
