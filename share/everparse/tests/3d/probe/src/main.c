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

// The type of input buffers passed to the secondary validator. With
// the Pulse backend, EVERPARSE_COPY_BUFFER_T is not opaque: it is a
// pointer to an EVERPARSE_COPY_BUFFER_DESCR, a plain struct declared
// in EverParse.h holding the three fields that make up a Pulse input
// stream, namely the base pointer `cb_base`, the length `cb_len` and
// a pointer `cb_pos` to the current read position.
//
// So, unlike with the Low* backend, there is no client-defined
// copy_buffer_t here, and no EverParseStreamOf/EverParseStreamLen to
// define either: the generated code reads `cb_base`/`cb_len`/`cb_pos`
// directly. The client only has to own the storage for the descriptor
// and for the position cell that `cb_pos` points to.

// THE PROBING FUNCTIONS

// `ProbeAndCopy` is a probing function declared in Probe.3d and the
// generated ../obj/Probe_ExternalAPI.h, but we need to define it by
// hand here. We define it as checking whether the pointer read from
// the `primary` type matches the `secondary` array, with the
// corresponding sizes, and if so, performing a copy from the
// `secondary` array to the buffer stored in dst->cb_base that will be
// used as an input buffer to the validator for the `secondary` type
// defined in Probe.3d.

BOOLEAN ProbeAndCopy(uint64_t len, uint64_t ro, uint64_t wo, uint64_t src, EVERPARSE_COPY_BUFFER_T dst) {
  static_assert(sizeof(secondary) == 4, "unexpected size of secondary");
  if (src == (uint64_t) secondary &&
      ro == 0 &&
      wo == 0 &&
      len == sizeof(secondary) && dst->cb_len >= (size_t) len) {
    memcpy(dst->cb_base, (uint8_t*) secondary, (size_t) len);
    return true;
  } else {
    printf("ProbeAndCopy failed\n");
    return false;
  }
}

BOOLEAN ProbeInit(const char* typename, uint64_t len, EVERPARSE_COPY_BUFFER_T dst) {
  return true;
}

// `ProbeInPlace` is a probing function declared in Probe.3d and the
// generated ../obj/Probe_ExternalAPI.h, but we need to define it by
// hand here. We define it as checking whether the pointer read from
// the `primary` type matches the `secondary` array, with the
// corresponding sizes, and if so, NOT performing a copy, but rather
// repointing the copy buffer at the `secondary` array, which the
// validator for the `secondary` type defined in Probe.3d will then
// use directly as its input.
//
// Repointing works because EVERPARSE_COPY_BUFFER_T is a *pointer* to
// the descriptor, exactly as in the Low* backend where it is an
// opaque pointer whose EverParseStreamOf the client may change.

BOOLEAN ProbeInPlace(
  uint64_t len,
  uint64_t read_offset,
  uint64_t write_offset,
  uint64_t src, 
  EVERPARSE_COPY_BUFFER_T dst
) {
  static_assert(sizeof(secondary) == 4, "unexpected size of secondary");
  if (src == (uint64_t) secondary &&
      read_offset == 0 &&
      write_offset == 0 &&
      len == sizeof(secondary)) {
    dst->cb_base = (uint8_t*) secondary;
    dst->cb_len = (size_t) len;
    return true;
  } else {
    printf("ProbeAndCopy failed\n");
    return false;
  }
}

// THE MAIN TEST FUNCTION

int main(void) {

  // In-place test: the ProbeInPlace probing function will repoint the
  // destination at the `secondary` array without a copy, so that the
  // `secondary` validator will directly use the `secondary` array as
  // an input. The initial base/length are therefore irrelevant; only
  // the position cell has to be backed by real storage, since the
  // generated code resets it through `cb_pos` before validating.
  size_t posInPlace = 0;
  EVERPARSE_COPY_BUFFER_DESCR destInPlace = {
    .cb_base = NULL,
    .cb_len = 0,
    .cb_pos = &posInPlace
  };
  static_assert(sizeof(primary) == 16, "unexpected size of primary");
  if (ProbeCheckPrimaryInPlace(&destInPlace, (uint8_t*) primary, sizeof(primary))) {
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
  static_assert (sizeof(destAndCopyBuf) == 8, "unexpected size of destAndCopyBuf");
  size_t posAndCopy = 0;
  EVERPARSE_COPY_BUFFER_DESCR destAndCopy = {
    .cb_base = destAndCopyBuf,
    .cb_len = sizeof(destAndCopyBuf),
    .cb_pos = &posAndCopy
  };
  if (ProbeCheckPrimaryAndCopy(&destAndCopy, (uint8_t*) primary, sizeof(primary))) {
    printf("Validation succeeded with PrimaryAndCopy\n");
  } else {
    printf("Validation failed with PrimaryAndCopy\n");
    return 1;
  }

  return 0;
}
