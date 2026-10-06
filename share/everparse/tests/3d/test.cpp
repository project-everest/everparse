#include "ArithmeticWrapper.h"
#include <stdint.h>
#include <iostream>
#include <cstring>

static_assert(EVERPARSE_VALIDATOR_SUCCESS == 0 && EVERPARSE_SUCCESS == 0,
              "success kind");
static_assert(EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED == 5 && EVERPARSE_ERROR_ACTION_FAILED == 5,
              "action failure kind");
static_assert(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA == 2 && EVERPARSE_ERROR_NOT_ENOUGH_DATA == 2,
              "insufficient data kind");
static_assert(EVERPARSE_VALIDATOR_ERROR_IMPOSSIBLE == 3 && EVERPARSE_ERROR_IMPOSSIBLE == 3,
              "impossible kind");
static_assert(EVERPARSE_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE == 4 && EVERPARSE_ERROR_LIST_SIZE_NOT_MULTIPLE == 4,
              "list size kind");
static_assert(EVERPARSE_VALIDATOR_ERROR_CONSTRAINT_FAILED == 6 && EVERPARSE_ERROR_CONSTRAINT_FAILED == 6,
              "constraint failure kind");
static_assert(EVERPARSE_VALIDATOR_ERROR_UNEXPECTED_PADDING == 7 && EVERPARSE_ERROR_UNEXPECTED_PADDING == 7,
              "padding failure kind");
static_assert(EVERPARSE_VALIDATOR_ERROR_PROBE_FAILED == 8 && EVERPARSE_ERROR_PROBE_FAILED == 8,
              "probe failure kind");

uint8_t test[20] = {
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9
};

extern "C"
void ArithmeticEverParseError(char *x, char *y, char *z) {
}

int main(int argc, char** argv) {
  const struct {
    uint8_t code;
    const char *reason;
  } errors[] = {
    {0, "success"},
    {1, "unspecified"},
    {2, "not enough data"},
    {3, "impossible"},
    {4, "list size not multiple of element size"},
    {5, "action failed"},
    {6, "constraint failed"},
    {7, "unexpected padding"},
    {8, "probe failed"},
    {9, "unspecified"},
    {255, "unspecified"}
  };
  for (const auto &error : errors) {
    if (std::strcmp(EverParseErrorReasonOfResult(error.code), error.reason) != 0) {
      std::cerr << "Wrong reason for error kind " << unsigned(error.code) << std::endl;
      return 1;
    }
  }
  if (! (ArithmeticCheckTest3(test, 20))) {
      std::cout << "Validation failed, but that's fine" << std::endl;
  } else {
      std::cout << "Validation succeeded" << std::endl;
  }
  return 0;
}
