#include "ArithWrapper.h"
#include <stdint.h>
#include <iostream>

uint8_t test[20] = {
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9
};

extern "C"
void ArithEverParseError(char *x, char *y, char *z) {
}

int main(int argc, char** argv) {
  if (! (ArithCheckTest3(test, 20))) {
      std::cout << "Validation failed, but that's fine" << std::endl;
  } else {
      std::cout << "Validation succeeded" << std::endl;
  }
  return 0;
}
