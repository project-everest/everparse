#include <stdint.h>
#include <iostream>
#include "AnonStructWrapper.h"

void AnonStructEverParseError(const char *StructName, const char *FieldName, const char *Reason)
{
}

using namespace std;

int main ()
{
  OTPOINT s1 = { 1, 2, 3 };
  OTPOINT s2;

  AnonStructCheckFlattpoint (&s2, (uint8_t *) &s1, 12);
  if (s2.x == 1 && s2.y == 2 && s2.z == 3) {
    std::cout << "Output types testcase (AnonStruct) success!" << std::endl;
    return 0;
  } else {
    std::cout << "Output types testcase (AnonStruct) err!" << std::endl;
    return 1;
  }
}
