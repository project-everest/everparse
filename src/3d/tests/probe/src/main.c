#include "ProbeWrapper.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

// THE INPUT BUFFERS

// We assume a little-endian C ABI.

// `secondary` will contain the input for the `secondary` type defined
// in Probe.3d. Depending on the probe function used (see below), it
// may be used either directly as an input buffer, or first copied
// into a separate temporary byte array.

uint16_t secondary[2] = {1, 2};

// `primary` will be the input buffer for both `primaryInPlace` and
// `primaryAndCopy` validators, containing a pointer to `secondary`

uint64_t primary[2] = {1, (uint64_t) (void*) secondary};

// THE COPY BUFFER TYPE AND OPERATIONS

// The type of input buffers passed to the secondary validator. In
// EverParse.h, EVERPARSE_COPY_BUFFER_T is defined as void*, but in
// our example here, we will use `copy_buffer_t*`

typedef struct {
  uint8_t *buf;
  uint64_t len;
} copy_buffer_t;

// `EverParseStreamOf` is declared in EverParse.h, but we need to
// define it here. Given an input buffer, `EverParseStreamOf` is
// intended to return the input byte array that will be passed to the
// `secondary` validator.

uint8_t * EverParseStreamOf(EVERPARSE_COPY_BUFFER_T x) {
  return ((copy_buffer_t *) x)->buf;
}

// `EverParseStreamLen` is declared in EverParse.h, but we need to
// define it here. Given an input buffer, `EverParseStreamLen` is
// intended to return the number of input bytes that the
// `secondary` validator is allowed to read.

uint64_t EverParseStreamLen(EVERPARSE_COPY_BUFFER_T x) {
  return ((copy_buffer_t *) x)->len;
}

// THE PROBING FUNCTIONS

// `ProbeAndCopy` is a probing function declared in Probe.3d and the
// generated ../obj/Probe_ExternalAPI.h, but we need to define it by
// hand here. We define it as checking whether the pointer read from
// the `primary` type matches the `secondary` array, with the
// corresponding sizes, and if so, performing a copy from the
// `secondary` array to the buffer stored in dst->buf that will be
// used as an input buffer to the validator for the `secondary` type
// defined in Probe.3d.

BOOLEAN ProbeAndCopy(uint64_t src, uint64_t len, EVERPARSE_COPY_BUFFER_T dst) {
  static_assert(sizeof(secondary) == 4);
  copy_buffer_t *p = dst;
  if (src == (uint64_t) secondary && len == sizeof(secondary) && p->len >= len) {
    memcpy(p->buf, (uint8_t*) secondary, len);
    return true;
  } else {
    printf("ProbeAndCopy failed\n");
    return false;
  }
}

// `ProbeInPlace` is a probing function declared in Probe.3d and the
// generated ../obj/Probe_ExternalAPI.h, but we need to define it by
// hand here. We define it as checking whether the pointer read from
// the `primary` type matches the `secondary` array, with the
// corresponding sizes, and if so, NOT performing a copy, but rather
// reusing the `secondary` array directly as an input buffer to the
// validator for the `secondary` type defined in Probe.3d.

BOOLEAN ProbeInPlace(uint64_t src, uint64_t len, EVERPARSE_COPY_BUFFER_T dst) {
  static_assert(sizeof(secondary) == 4);
  if (src == (uint64_t) secondary && len == sizeof(secondary)) {
    copy_buffer_t *p = dst;
    p->buf = (uint8_t*) secondary;
    p->len = len;
    return true;
  } else {
    printf("ProbeAndCopy failed\n");
    return false;
  }
}

// THE MAIN TEST FUNCTION

int main(void) {

  // In-place test: the ProbeInPlace probing function will populate
  // the destination directly with the `secondary` array without a
  // copy, so that the `secondary` validator will directly use the
  // `secondary` array as an input
  copy_buffer_t destInPlace = (copy_buffer_t) {
    .buf = NULL,
    .len = 0
  };
  static_assert(sizeof(primary) == 16);
  if (ProbeCheckPrimaryInPlace((EVERPARSE_COPY_BUFFER_T) &destInPlace, (uint8_t*) primary, sizeof(primary))) {
    printf("Validation succeeded with PrimaryInPlace\n");
  } else {
    printf("Validation failed with PrimaryInPlace\n");
    return 1;
  }

  // Test with copy: the ProbeAndCopy probing function will copy the
  // `secondary` array to the temporary `destAndCopyBuf` array below,
  // which will then be used by the `secondary` validator. The size of
  // the copy buffer must be greater or equal to the size used in the
  // `probe` declaration in Probe.3d.
  uint8_t destAndCopyBuf[8];
  static_assert (sizeof(destAndCopyBuf) == 8);
  copy_buffer_t destAndCopy = (copy_buffer_t) {
    .buf = destAndCopyBuf,
    .len = sizeof(destAndCopyBuf)
  };
  if (ProbeCheckPrimaryAndCopy((EVERPARSE_COPY_BUFFER_T) &destAndCopy, (uint8_t*) primary, sizeof(primary))) {
    printf("Validation succeeded with PrimaryAndCopy\n");
  } else {
    printf("Validation failed with PrimaryAndCopy\n");
    return 1;
  }

  return 0;
}
