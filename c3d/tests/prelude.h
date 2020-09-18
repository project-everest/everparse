// A set of definitions for MSVC-isms that make the files parsable and workable
// with. Use -include to prepend this file.

#pragma once

#include <stdint.h>
#include <stdbool.h>

#define UINT8 uint8_t
#define UINT16 uint16_t
#define UINT32 uint32_t
#define UINT64 uint64_t

bool is_range_okay(uint32_t x, uint32_t y, uint32_t z);
