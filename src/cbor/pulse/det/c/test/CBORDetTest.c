
#include <string.h>
#include <stdio.h>
#include <inttypes.h>
#include "CBORDet.h"
#include "CBORDetTest.h"

static char * hex_digits[16] = {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f"};

static Pulse_Lib_Slice_slice__uint8_t mk_byte_slice (uint8_t *elt, size_t len) {
  return (Pulse_Lib_Slice_slice__uint8_t) { elt = elt, len = len };
}

static void dump_encoding_test_failure (uint8_t *bytes, size_t len) {
  size_t pos = 0;
  printf("Encoded bytes: ");
  while (pos < len) {
    uint8_t x = bytes[pos];
    printf("%s%s", hex_digits[x / 16], hex_digits[x % 16]);
    pos += 1;
  };
  printf("\n");
}

int gentest(void) {
  {
    printf("Test 1 out of 29\n");
    printf("Testing: ""0""\n");
    uint8_t source_bytes[1] = {0x00};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,0);
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 00\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 2 out of 29\n");
    printf("Testing: ""1""\n");
    uint8_t source_bytes[1] = {0x01};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,1);
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 01\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 3 out of 29\n");
    printf("Testing: ""10""\n");
    uint8_t source_bytes[1] = {0x0a};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,10);
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 0a\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 4 out of 29\n");
    printf("Testing: ""23""\n");
    uint8_t source_bytes[1] = {0x17};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,23);
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 17\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 5 out of 29\n");
    printf("Testing: ""24""\n");
    uint8_t source_bytes[2] = {0x18, 0x18};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,24);
    uint8_t target_bytes[2];
    size_t target_byte_size = cbor_det_size(source_cbor, 2);
    if (target_byte_size != 2)
    {
      printf("Size computation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Encoding failed: expected 2 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 2);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 1818\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Validation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 2), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 6 out of 29\n");
    printf("Testing: ""25""\n");
    uint8_t source_bytes[2] = {0x18, 0x19};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,25);
    uint8_t target_bytes[2];
    size_t target_byte_size = cbor_det_size(source_cbor, 2);
    if (target_byte_size != 2)
    {
      printf("Size computation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Encoding failed: expected 2 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 2);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 1819\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Validation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 2), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 7 out of 29\n");
    printf("Testing: ""100""\n");
    uint8_t source_bytes[2] = {0x18, 0x64};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,100);
    uint8_t target_bytes[2];
    size_t target_byte_size = cbor_det_size(source_cbor, 2);
    if (target_byte_size != 2)
    {
      printf("Size computation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Encoding failed: expected 2 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 2);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 1864\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Validation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 2), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 8 out of 29\n");
    printf("Testing: ""1000""\n");
    uint8_t source_bytes[3] = {0x19, 0x03, 0xe8};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,1000);
    uint8_t target_bytes[3];
    size_t target_byte_size = cbor_det_size(source_cbor, 3);
    if (target_byte_size != 3)
    {
      printf("Size computation failed: expected 3 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 3));
    if (target_byte_size != 3)
    {
      printf("Encoding failed: expected 3 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 3);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 1903e8\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 3));
    if (target_byte_size != 3)
    {
      printf("Validation failed: expected 3 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 3), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 9 out of 29\n");
    printf("Testing: ""1000000""\n");
    uint8_t source_bytes[5] = {0x1a, 0x00, 0x0f, 0x42, 0x40};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,1000000);
    uint8_t target_bytes[5];
    size_t target_byte_size = cbor_det_size(source_cbor, 5);
    if (target_byte_size != 5)
    {
      printf("Size computation failed: expected 5 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 5));
    if (target_byte_size != 5)
    {
      printf("Encoding failed: expected 5 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 5);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 1a000f4240\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 5));
    if (target_byte_size != 5)
    {
      printf("Validation failed: expected 5 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 5), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 10 out of 29\n");
    printf("Testing: ""1000000000000""\n");
    uint8_t source_bytes[9] = {0x1b, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,1000000000000);
    uint8_t target_bytes[9];
    size_t target_byte_size = cbor_det_size(source_cbor, 9);
    if (target_byte_size != 9)
    {
      printf("Size computation failed: expected 9 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 9));
    if (target_byte_size != 9)
    {
      printf("Encoding failed: expected 9 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 9);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 1b000000e8d4a51000\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 9));
    if (target_byte_size != 9)
    {
      printf("Validation failed: expected 9 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 9), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 11 out of 29\n");
    printf("Testing: ""-1""\n");
    uint8_t source_bytes[1] = {0x20};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64,0);
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 20\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 12 out of 29\n");
    printf("Testing: ""-10""\n");
    uint8_t source_bytes[1] = {0x29};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64,9);
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 29\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 13 out of 29\n");
    printf("Testing: ""-100""\n");
    uint8_t source_bytes[2] = {0x38, 0x63};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64,99);
    uint8_t target_bytes[2];
    size_t target_byte_size = cbor_det_size(source_cbor, 2);
    if (target_byte_size != 2)
    {
      printf("Size computation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Encoding failed: expected 2 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 2);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 3863\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Validation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 2), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 14 out of 29\n");
    printf("Testing: ""-1000""\n");
    uint8_t source_bytes[3] = {0x39, 0x03, 0xe7};
    cbor_det_t source_cbor = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64,999);
    uint8_t target_bytes[3];
    size_t target_byte_size = cbor_det_size(source_cbor, 3);
    if (target_byte_size != 3)
    {
      printf("Size computation failed: expected 3 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 3));
    if (target_byte_size != 3)
    {
      printf("Encoding failed: expected 3 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 3);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 3903e7\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 3));
    if (target_byte_size != 3)
    {
      printf("Validation failed: expected 3 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 3), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 15 out of 29\n");
    printf("Testing: ""\"\"""\n");
    uint8_t source_bytes[1] = {0x60};
    cbor_det_t source_cbor = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"", 0));
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 60\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 16 out of 29\n");
    printf("Testing: ""\"a\"""\n");
    uint8_t source_bytes[2] = {0x61, 0x61};
    cbor_det_t source_cbor = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"a", 1));
    uint8_t target_bytes[2];
    size_t target_byte_size = cbor_det_size(source_cbor, 2);
    if (target_byte_size != 2)
    {
      printf("Size computation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Encoding failed: expected 2 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 2);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 6161\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 2));
    if (target_byte_size != 2)
    {
      printf("Validation failed: expected 2 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 2), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 17 out of 29\n");
    printf("Testing: ""\"IETF\"""\n");
    uint8_t source_bytes[5] = {0x64, 0x49, 0x45, 0x54, 0x46};
    cbor_det_t source_cbor = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"IETF", 4));
    uint8_t target_bytes[5];
    size_t target_byte_size = cbor_det_size(source_cbor, 5);
    if (target_byte_size != 5)
    {
      printf("Size computation failed: expected 5 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 5));
    if (target_byte_size != 5)
    {
      printf("Encoding failed: expected 5 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 5);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 6449455446\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 5));
    if (target_byte_size != 5)
    {
      printf("Validation failed: expected 5 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 5), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 18 out of 29\n");
    printf("Testing: ""\"\\\"\\\\\"""\n");
    uint8_t source_bytes[3] = {0x62, 0x22, 0x5c};
    cbor_det_t source_cbor = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"\"\\", 2));
    uint8_t target_bytes[3];
    size_t target_byte_size = cbor_det_size(source_cbor, 3);
    if (target_byte_size != 3)
    {
      printf("Size computation failed: expected 3 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 3));
    if (target_byte_size != 3)
    {
      printf("Encoding failed: expected 3 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 3);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 62225c\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 3));
    if (target_byte_size != 3)
    {
      printf("Validation failed: expected 3 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 3), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 19 out of 29\n");
    printf("Testing: ""\"ü\"""\n");
    uint8_t source_bytes[3] = {0x62, 0xc3, 0xbc};
    cbor_det_t source_cbor = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"ü", 2));
    uint8_t target_bytes[3];
    size_t target_byte_size = cbor_det_size(source_cbor, 3);
    if (target_byte_size != 3)
    {
      printf("Size computation failed: expected 3 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 3));
    if (target_byte_size != 3)
    {
      printf("Encoding failed: expected 3 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 3);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 62c3bc\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 3));
    if (target_byte_size != 3)
    {
      printf("Validation failed: expected 3 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 3), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 20 out of 29\n");
    printf("Testing: ""\"水\"""\n");
    uint8_t source_bytes[4] = {0x63, 0xe6, 0xb0, 0xb4};
    cbor_det_t source_cbor = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"水", 3));
    uint8_t target_bytes[4];
    size_t target_byte_size = cbor_det_size(source_cbor, 4);
    if (target_byte_size != 4)
    {
      printf("Size computation failed: expected 4 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 4));
    if (target_byte_size != 4)
    {
      printf("Encoding failed: expected 4 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 4);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 63e6b0b4\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 4));
    if (target_byte_size != 4)
    {
      printf("Validation failed: expected 4 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 4), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 21 out of 29\n");
    printf("Testing: ""\"𐅑\"""\n");
    uint8_t source_bytes[5] = {0x64, 0xf0, 0x90, 0x85, 0x91};
    cbor_det_t source_cbor = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"𐅑", 4));
    uint8_t target_bytes[5];
    size_t target_byte_size = cbor_det_size(source_cbor, 5);
    if (target_byte_size != 5)
    {
      printf("Size computation failed: expected 5 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 5));
    if (target_byte_size != 5)
    {
      printf("Encoding failed: expected 5 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 5);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 64f0908591\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 5));
    if (target_byte_size != 5)
    {
      printf("Validation failed: expected 5 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 5), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 22 out of 29\n");
    printf("Testing: ""[]""\n");
    uint8_t source_bytes[1] = {0x80};
    cbor_det_t source_cbor_array[0];
    cbor_det_t source_cbor = cbor_det_mk_array(source_cbor_array, 0);
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 80\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 23 out of 29\n");
    printf("Testing: ""[1,2,3]""\n");
    uint8_t source_bytes[4] = {0x83, 0x01, 0x02, 0x03};
    cbor_det_t source_cbor_array[3];
    cbor_det_t source_cbor_map_2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,3);
    source_cbor_array[2] = source_cbor_map_2;
    cbor_det_t source_cbor_map_1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,2);
    source_cbor_array[1] = source_cbor_map_1;
    cbor_det_t source_cbor_map_0 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,1);
    source_cbor_array[0] = source_cbor_map_0;
    cbor_det_t source_cbor = cbor_det_mk_array(source_cbor_array, 3);
    uint8_t target_bytes[4];
    size_t target_byte_size = cbor_det_size(source_cbor, 4);
    if (target_byte_size != 4)
    {
      printf("Size computation failed: expected 4 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 4));
    if (target_byte_size != 4)
    {
      printf("Encoding failed: expected 4 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 4);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 83010203\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 4));
    if (target_byte_size != 4)
    {
      printf("Validation failed: expected 4 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 4), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 24 out of 29\n");
    printf("Testing: ""[1,[2,3],[4,5]]""\n");
    uint8_t source_bytes[8] = {0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05};
    cbor_det_t source_cbor_array[3];
    cbor_det_t source_cbor_map_2_array[2];
    cbor_det_t source_cbor_map_2_map_1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,5);
    source_cbor_map_2_array[1] = source_cbor_map_2_map_1;
    cbor_det_t source_cbor_map_2_map_0 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,4);
    source_cbor_map_2_array[0] = source_cbor_map_2_map_0;
    cbor_det_t source_cbor_map_2 = cbor_det_mk_array(source_cbor_map_2_array, 2);
    source_cbor_array[2] = source_cbor_map_2;
    cbor_det_t source_cbor_map_1_array[2];
    cbor_det_t source_cbor_map_1_map_1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,3);
    source_cbor_map_1_array[1] = source_cbor_map_1_map_1;
    cbor_det_t source_cbor_map_1_map_0 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,2);
    source_cbor_map_1_array[0] = source_cbor_map_1_map_0;
    cbor_det_t source_cbor_map_1 = cbor_det_mk_array(source_cbor_map_1_array, 2);
    source_cbor_array[1] = source_cbor_map_1;
    cbor_det_t source_cbor_map_0 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,1);
    source_cbor_array[0] = source_cbor_map_0;
    cbor_det_t source_cbor = cbor_det_mk_array(source_cbor_array, 3);
    uint8_t target_bytes[8];
    size_t target_byte_size = cbor_det_size(source_cbor, 8);
    if (target_byte_size != 8)
    {
      printf("Size computation failed: expected 8 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 8));
    if (target_byte_size != 8)
    {
      printf("Encoding failed: expected 8 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 8);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 8301820203820405\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 8));
    if (target_byte_size != 8)
    {
      printf("Validation failed: expected 8 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 8), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 25 out of 29\n");
    printf("Testing: ""[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25]""\n");
    uint8_t source_bytes[29] = {0x98, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19};
    cbor_det_t source_cbor_array[25];
    cbor_det_t source_cbor_map_24 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,25);
    source_cbor_array[24] = source_cbor_map_24;
    cbor_det_t source_cbor_map_23 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,24);
    source_cbor_array[23] = source_cbor_map_23;
    cbor_det_t source_cbor_map_22 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,23);
    source_cbor_array[22] = source_cbor_map_22;
    cbor_det_t source_cbor_map_21 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,22);
    source_cbor_array[21] = source_cbor_map_21;
    cbor_det_t source_cbor_map_20 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,21);
    source_cbor_array[20] = source_cbor_map_20;
    cbor_det_t source_cbor_map_19 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,20);
    source_cbor_array[19] = source_cbor_map_19;
    cbor_det_t source_cbor_map_18 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,19);
    source_cbor_array[18] = source_cbor_map_18;
    cbor_det_t source_cbor_map_17 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,18);
    source_cbor_array[17] = source_cbor_map_17;
    cbor_det_t source_cbor_map_16 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,17);
    source_cbor_array[16] = source_cbor_map_16;
    cbor_det_t source_cbor_map_15 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,16);
    source_cbor_array[15] = source_cbor_map_15;
    cbor_det_t source_cbor_map_14 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,15);
    source_cbor_array[14] = source_cbor_map_14;
    cbor_det_t source_cbor_map_13 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,14);
    source_cbor_array[13] = source_cbor_map_13;
    cbor_det_t source_cbor_map_12 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,13);
    source_cbor_array[12] = source_cbor_map_12;
    cbor_det_t source_cbor_map_11 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,12);
    source_cbor_array[11] = source_cbor_map_11;
    cbor_det_t source_cbor_map_10 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,11);
    source_cbor_array[10] = source_cbor_map_10;
    cbor_det_t source_cbor_map_9 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,10);
    source_cbor_array[9] = source_cbor_map_9;
    cbor_det_t source_cbor_map_8 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,9);
    source_cbor_array[8] = source_cbor_map_8;
    cbor_det_t source_cbor_map_7 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,8);
    source_cbor_array[7] = source_cbor_map_7;
    cbor_det_t source_cbor_map_6 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,7);
    source_cbor_array[6] = source_cbor_map_6;
    cbor_det_t source_cbor_map_5 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,6);
    source_cbor_array[5] = source_cbor_map_5;
    cbor_det_t source_cbor_map_4 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,5);
    source_cbor_array[4] = source_cbor_map_4;
    cbor_det_t source_cbor_map_3 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,4);
    source_cbor_array[3] = source_cbor_map_3;
    cbor_det_t source_cbor_map_2 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,3);
    source_cbor_array[2] = source_cbor_map_2;
    cbor_det_t source_cbor_map_1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,2);
    source_cbor_array[1] = source_cbor_map_1;
    cbor_det_t source_cbor_map_0 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,1);
    source_cbor_array[0] = source_cbor_map_0;
    cbor_det_t source_cbor = cbor_det_mk_array(source_cbor_array, 25);
    uint8_t target_bytes[29];
    size_t target_byte_size = cbor_det_size(source_cbor, 29);
    if (target_byte_size != 29)
    {
      printf("Size computation failed: expected 29 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 29));
    if (target_byte_size != 29)
    {
      printf("Encoding failed: expected 29 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 29);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 98190102030405060708090a0b0c0d0e0f101112131415161718181819\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 29));
    if (target_byte_size != 29)
    {
      printf("Validation failed: expected 29 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 29), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 26 out of 29\n");
    printf("Testing: ""{}""\n");
    uint8_t source_bytes[1] = {0xa0};
    cbor_map_entry source_cbor_map[0];
    cbor_det_t source_cbor = cbor_det_mk_map(source_cbor_map, 0);
    uint8_t target_bytes[1];
    size_t target_byte_size = cbor_det_size(source_cbor, 1);
    if (target_byte_size != 1)
    {
      printf("Size computation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Encoding failed: expected 1 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 1);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected a0\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 1));
    if (target_byte_size != 1)
    {
      printf("Validation failed: expected 1 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 1), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 27 out of 29\n");
    printf("Testing: ""{\"a\":1,\"b\":[2,3]}""\n");
    uint8_t source_bytes[9] = {0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03};
    cbor_map_entry source_cbor_map[2];
    cbor_det_t source_cbor_map_1_key = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"b", 1));
    cbor_det_t source_cbor_map_1_value_array[2];
    cbor_det_t source_cbor_map_1_value_map_1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,3);
    source_cbor_map_1_value_array[1] = source_cbor_map_1_value_map_1;
    cbor_det_t source_cbor_map_1_value_map_0 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,2);
    source_cbor_map_1_value_array[0] = source_cbor_map_1_value_map_0;
    cbor_det_t source_cbor_map_1_value = cbor_det_mk_array(source_cbor_map_1_value_array, 2);
    source_cbor_map[1] = (cbor_map_entry) {.cbor_map_entry_key = source_cbor_map_1_key, .cbor_map_entry_value = source_cbor_map_1_value};
    cbor_det_t source_cbor_map_0_key = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"a", 1));
    cbor_det_t source_cbor_map_0_value = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64,1);
    source_cbor_map[0] = (cbor_map_entry) {.cbor_map_entry_key = source_cbor_map_0_key, .cbor_map_entry_value = source_cbor_map_0_value};
    cbor_det_t source_cbor = cbor_det_mk_map(source_cbor_map, 2);
    uint8_t target_bytes[9];
    size_t target_byte_size = cbor_det_size(source_cbor, 9);
    if (target_byte_size != 9)
    {
      printf("Size computation failed: expected 9 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 9));
    if (target_byte_size != 9)
    {
      printf("Encoding failed: expected 9 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 9);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected a26161016162820203\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 9));
    if (target_byte_size != 9)
    {
      printf("Validation failed: expected 9 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 9), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 28 out of 29\n");
    printf("Testing: ""[\"a\",{\"b\":\"c\"}]""\n");
    uint8_t source_bytes[8] = {0x82, 0x61, 0x61, 0xa1, 0x61, 0x62, 0x61, 0x63};
    cbor_det_t source_cbor_array[2];
    cbor_map_entry source_cbor_map_1_map[1];
    cbor_det_t source_cbor_map_1_map_0_key = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"b", 1));
    cbor_det_t source_cbor_map_1_map_0_value = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"c", 1));
    source_cbor_map_1_map[0] = (cbor_map_entry) {.cbor_map_entry_key = source_cbor_map_1_map_0_key, .cbor_map_entry_value = source_cbor_map_1_map_0_value};
    cbor_det_t source_cbor_map_1 = cbor_det_mk_map(source_cbor_map_1_map, 1);
    source_cbor_array[1] = source_cbor_map_1;
    cbor_det_t source_cbor_map_0 = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"a", 1));
    source_cbor_array[0] = source_cbor_map_0;
    cbor_det_t source_cbor = cbor_det_mk_array(source_cbor_array, 2);
    uint8_t target_bytes[8];
    size_t target_byte_size = cbor_det_size(source_cbor, 8);
    if (target_byte_size != 8)
    {
      printf("Size computation failed: expected 8 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 8));
    if (target_byte_size != 8)
    {
      printf("Encoding failed: expected 8 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 8);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected 826161a161626163\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 8));
    if (target_byte_size != 8)
    {
      printf("Validation failed: expected 8 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 8), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }
  {
    printf("Test 29 out of 29\n");
    printf("Testing: ""{\"a\":\"A\",\"b\":\"B\",\"c\":\"C\",\"d\":\"D\",\"e\":\"E\"}""\n");
    uint8_t source_bytes[21] = {0xa5, 0x61, 0x61, 0x61, 0x41, 0x61, 0x62, 0x61, 0x42, 0x61, 0x63, 0x61, 0x43, 0x61, 0x64, 0x61, 0x44, 0x61, 0x65, 0x61, 0x45};
    cbor_map_entry source_cbor_map[5];
    cbor_det_t source_cbor_map_4_key = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"e", 1));
    cbor_det_t source_cbor_map_4_value = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"E", 1));
    source_cbor_map[4] = (cbor_map_entry) {.cbor_map_entry_key = source_cbor_map_4_key, .cbor_map_entry_value = source_cbor_map_4_value};
    cbor_det_t source_cbor_map_3_key = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"d", 1));
    cbor_det_t source_cbor_map_3_value = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"D", 1));
    source_cbor_map[3] = (cbor_map_entry) {.cbor_map_entry_key = source_cbor_map_3_key, .cbor_map_entry_value = source_cbor_map_3_value};
    cbor_det_t source_cbor_map_2_key = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"c", 1));
    cbor_det_t source_cbor_map_2_value = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"C", 1));
    source_cbor_map[2] = (cbor_map_entry) {.cbor_map_entry_key = source_cbor_map_2_key, .cbor_map_entry_value = source_cbor_map_2_value};
    cbor_det_t source_cbor_map_1_key = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"b", 1));
    cbor_det_t source_cbor_map_1_value = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"B", 1));
    source_cbor_map[1] = (cbor_map_entry) {.cbor_map_entry_key = source_cbor_map_1_key, .cbor_map_entry_value = source_cbor_map_1_value};
    cbor_det_t source_cbor_map_0_key = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"a", 1));
    cbor_det_t source_cbor_map_0_value = cbor_det_mk_string(CBOR_MAJOR_TYPE_TEXT_STRING, mk_byte_slice((uint8_t *)"A", 1));
    source_cbor_map[0] = (cbor_map_entry) {.cbor_map_entry_key = source_cbor_map_0_key, .cbor_map_entry_value = source_cbor_map_0_value};
    cbor_det_t source_cbor = cbor_det_mk_map(source_cbor_map, 5);
    uint8_t target_bytes[21];
    size_t target_byte_size = cbor_det_size(source_cbor, 21);
    if (target_byte_size != 21)
    {
      printf("Size computation failed: expected 21 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    target_byte_size = cbor_det_serialize (source_cbor, mk_byte_slice(target_bytes, 21));
    if (target_byte_size != 21)
    {
      printf("Encoding failed: expected 21 bytes, wrote %ld\n", target_byte_size);
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    int compare_encoding = memcmp(source_bytes, target_bytes, 21);
    if (compare_encoding != 0)
    {
      printf("Encoding mismatch: expected a56161614161626142616361436164614461656145\n");
      dump_encoding_test_failure(target_bytes, target_byte_size);
      return 1;
    }
    printf("Encoding succeeded!\n");
    target_byte_size = cbor_det_validate(mk_byte_slice(source_bytes, 21));
    if (target_byte_size != 21)
    {
      printf("Validation failed: expected 21 bytes, got %ld\n", target_byte_size);
      return 1;
    }
    printf("Validation succeeded!\n");
    cbor_det_t target_cbor = cbor_det_parse(mk_byte_slice(source_bytes, 21), target_byte_size);
    printf("Parsing succeeded!\n");
    if (! (cbor_det_equal(source_cbor, target_cbor)))
    {
      printf("Decoding mismatch!\n");
      return 1;
    }
    printf("Decoding succeeded!\n");
  }

  return 0;
}

