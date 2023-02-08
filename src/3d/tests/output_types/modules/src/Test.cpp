#include <stdint.h>
#include <iostream>

#include "BBWrapper.h"
#include "CCWrapper.h"

using namespace std;

void BBEverParseError(const char *StructName, const char *FieldName, const char *Reason)
{
  std::cout << "Validation failed" << std::endl;
}

void CCEverParseError(const char *StructName, const char *FieldName, const char *Reason)
{
  std::cout << "Validation failed" << std::endl;
}

int main ()
{
  return 0;
}
