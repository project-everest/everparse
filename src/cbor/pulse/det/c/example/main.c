/* This file is a documented example of how to use the CBORDet C API */

#include <string.h>
#include <stdio.h>
#include <inttypes.h>
#include <assert.h>

/* CBORDet.h defines the CBORDet C API */
#include "CBORDet.h"

int main(void) {

  /* 1. Creating CBOR objects */

  /* Stack-allocate an unsigned integer object (major type 0) of value x */
  uint64_t x = 1729;
  cbor_det_t cbor0 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, x);

  /* Stack-allocate an unsigned integer object (major type 1) of value -1-x */
  cbor_det_t cbor1 = cbor_det_mk_int64(CBOR_MAJOR_TYPE_NEG_INT64, x);

  /* Stack-allocate a byte string object (major type 2) */
  #define my_bytes_len 4
  uint8_t my_bytes[my_bytes_len] = { 18, 42, 17, 29 };
  cbor_det_t cbor2 = cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_BYTE_STRING, my_bytes, my_bytes_len);

  /* Stack-allocate a text string object (major type 3) */
  uint8_t * my_string = "Hello world!";
  assert (sizeof(my_string) > 0);
  uint64_t my_string_len = sizeof(my_string) - 1; // we don't want the null terminator
  cbor_det_t cbor3 = cbor_det_mk_string_from_arrayptr(CBOR_MAJOR_TYPE_TEXT_STRING, my_string, my_string_len);

  /* Stack-allocate an array object (major type 4) with array elements cbor0 and cbor1 */
  #define my_array_len 2
  cbor_det_t my_array[my_array_len] = { cbor0, cbor1 };
  cbor_det_t cbor4 = cbor_det_mk_array_from_array(my_array, my_array_len);

  /* Stack-allocate a map object (major type 5) with map entries (cbor0, cbor1) and (cbor2, cbor3)

     NOTE: cbor_det_mk_map_from_array_safe mutates the input array by
     reordering its entries according to their key serialization
     order.
  */
  #define my_map_len 2
  cbor_map_entry my_entry0 = cbor_det_mk_map_entry(cbor0, cbor1);
  cbor_map_entry my_entry1 = cbor_det_mk_map_entry(cbor2, cbor3);
  cbor_map_entry my_map[my_map_len] = { my_entry0, my_entry1 };
  cbor_det_t cbor5 = dummy_cbor_det_t();
  bool result5 = cbor_det_mk_map_from_array_safe(my_map, my_map_len, &cbor5);
  assert (result5);

  /* Tries to stack-allocate a map object with map entries (cbor0,
     cbor1) and (cbor0, cbor3) (notice the duplicate keys.) Then,
     cbor_det_mk_map_from_array_safe will gracefully fail
  */
  cbor_map_entry my_entry1_fail = cbor_det_mk_map_entry(cbor0, cbor3);
  cbor_map_entry my_map_fail[my_map_len] = { my_entry0, my_entry1_fail };
  cbor_det_t cbor5_fail = dummy_cbor_det_t();
  assert (! cbor_det_mk_map_from_array_safe(my_map_fail, my_map_len, &cbor5_fail));
  
  /* Stack-allocate a tagged object (major type 6) with payload cbor0
     Note that cbor_det_mk_tagged takes a pointer to the payload
  */
  uint64_t my_tag = 42;
  cbor_det_t cbor6 = cbor_det_mk_tagged(my_tag, &cbor0);

  /* Stack-allocate a simple value object (major type 7).
     TODO: add support for floats.
  */
  uint8_t my_simple = 18;
  cbor_det_t cbor7 = cbor_det_mk_simple_value(my_simple);


  /* 2. Reading values from CBOR objects */

  /* Determine the major type of a CBOR object */
  uint8_t major_type0 = cbor_det_major_type(cbor0);
  assert (major_type0 == CBOR_MAJOR_TYPE_UINT64);
  
  /* Read the value of an integer object (major type 0 or 1). Requires
     cbor_det_major_type to return CBOR_MAJOR_TYPE_UINT64 or
     CBOR_MAJOR_TYPE_NEG_INT64. In the case of a negative integer, the
     value returned is its one's complement (-1-x).
  */
  uint64_t read0 = cbor_det_read_uint64(cbor0);
  assert (read0 == x);
  assert (cbor_det_major_type(cbor1) == CBOR_MAJOR_TYPE_NEG_INT64);
  uint64_t read1 = cbor_det_read_uint64(cbor1);
  assert (read1 == x);

  /* Get the length of the byte payload of a byte or text string
     (major type 2 or 3). Requires cbor_det_major_type to return
     CBOR_MAJOR_TYPE_BYTE_STRING or CBOR_MAJOR_TYPE_TEXT_STRING. */
  assert (cbor_det_major_type(cbor2) == CBOR_MAJOR_TYPE_BYTE_STRING);
  uint64_t payload_size2 = cbor_det_get_string_length(cbor2);
  assert (payload_size2 == my_bytes_len);
  assert (cbor_det_major_type(cbor3) == CBOR_MAJOR_TYPE_TEXT_STRING);
  assert (cbor_det_get_string_length(cbor3) == my_string_len);

  /* Get a pointer to the byte payload of a byte or text string
     (major type 2 or 3). Requires cbor_det_major_type to return
     CBOR_MAJOR_TYPE_BYTE_STRING or CBOR_MAJOR_TYPE_TEXT_STRING. */
  uint8_t * cbor2_payload = cbor_det_get_string(cbor2);
  assert (memcmp(my_bytes, cbor2_payload, my_bytes_len) == 0);
  assert (memcmp(my_string, cbor_det_get_string(cbor3), my_string_len) == 0);

  /* Get the length of a CBOR array object (major type 4.) Requires
     cbor_det_major_type to return CBOR_MAJOR_TYPE_ARRAY */
  assert (cbor_det_major_type(cbor4) == CBOR_MAJOR_TYPE_ARRAY);
  uint64_t array_len4 = cbor_det_get_array_length(cbor4);
  assert (array_len4 == my_array_len);

  /* Get the nth item of a CBOR array object (major type 4.) Requires
     cbor_det_major_type to return CBOR_MAJOR_TYPE_ARRAY */
  uint64_t array_index = 1;
  cbor_det_t array_item = cbor_det_get_array_item(cbor4, array_index);
  assert (cbor_det_major_type(array_item) == CBOR_MAJOR_TYPE_NEG_INT64);
  assert (cbor_det_read_uint64(array_item) == x);

  /* Stack-allocate an iterator over the items of a CBOR array object
     (major type 4.) Requires cbor_det_major_type to return
     CBOR_MAJOR_TYPE_ARRAY */
  cbor_det_array_iterator_t array_iter = cbor_det_array_iterator_start(cbor4);
  while (! cbor_det_array_iterator_is_empty(array_iter)) {
    // note the pointer here
    cbor_det_t item = cbor_det_array_iterator_next(&array_iter);
    uint8_t item_type = cbor_det_major_type(item);
    assert (item_type == CBOR_MAJOR_TYPE_UINT64 || item_type == CBOR_MAJOR_TYPE_NEG_INT64);
  }

  /* Get the number of entries of a CBOR map object (major type 5.) Requires
     cbor_det_major_type to return CBOR_MAJOR_TYPE_MAP */
  assert (cbor_det_major_type(cbor5) == CBOR_MAJOR_TYPE_MAP);
  uint64_t map_len5 = cbor_det_get_map_length(cbor5);
  assert (map_len5 == my_map_len);

  /* Lookup an entry in a map by its key. Requires cbor_det_major_type
     to return CBOR_MAJOR_TYPE_MAP. cbor_det_map_get returns true if
     and only if there is an entry for the key, and if so, updates the
     outparameter with the value part of the entry. */
  // success
  cbor_det_t key = cbor_det_mk_int64(CBOR_MAJOR_TYPE_UINT64, x);
  cbor_det_t value = dummy_cbor_det_t();
  bool lookup = cbor_det_map_get(cbor5, key, &value);
  assert (lookup);
  assert (cbor_det_major_type(value) == CBOR_MAJOR_TYPE_NEG_INT64);
  assert (cbor_det_read_uint64(value) == x);
  // failure
  assert (! cbor_det_map_get(cbor5, cbor1, &value));

  /* Stack-allocate an iterator over the items of a CBOR map object
     (major type 5.) Requires cbor_det_major_type to return
     CBOR_MAJOR_TYPE_ARRAY */
  cbor_det_map_iterator_t map_iter = cbor_det_map_iterator_start(cbor5);
  while (! cbor_det_map_iterator_is_empty(map_iter)) {
    // note the pointer here
    cbor_map_entry entry = cbor_det_map_iterator_next(&map_iter);
    cbor_det_t entry_key = cbor_det_map_entry_key(entry);
    cbor_det_t entry_value = cbor_det_map_entry_value(entry);
  }

  /* Get the tag of a CBOR tag object (major type 6.) Requires
     cbor_det_major_type to return CBOR_MAJOR_TYPE_TAGGED */
  assert (cbor_det_major_type(cbor6) == CBOR_MAJOR_TYPE_TAGGED);
  uint64_t tag = cbor_det_get_tagged_tag(cbor6);
  assert (tag == my_tag);

  /* Get the payload of a CBOR tag object (major type 6.) Requires
     cbor_det_major_type to return CBOR_MAJOR_TYPE_TAGGED */
  cbor_det_t cbor6_payload = cbor_det_get_tagged_payload(cbor6);
  assert (cbor_det_major_type(cbor6_payload) == CBOR_MAJOR_TYPE_UINT64);
  assert (cbor_det_read_uint64(cbor6_payload) == x);

  /* Get the value of a CBOR simple value object (major type 7.)
     Requires cbor_det_major_type to return CBOR_MAJOR_TYPE_SIMPLE_VALUE */
  assert (cbor_det_major_type(cbor7) == CBOR_MAJOR_TYPE_SIMPLE_VALUE);
  uint8_t value7 = cbor_det_read_simple_value(cbor7);
  assert (value7 == my_simple);

  /* Compare two CBOR objects for equality. */
  // success
  bool compare = cbor_det_equal(cbor0, cbor6_payload);
  assert (compare);
  // failure
  assert (! (cbor_det_equal(cbor0, cbor1)));
  
  
  /* 3. Serialization */

  /* Compute the byte size of the deterministic encoding of a CBOR
     object. cbor_det_size takes a bound, and returns either 0 if the
     size of the object is strictly larger than the bound, or the size
     of the object, which is a positive integer. */
  // success
  #define output_size 42
  size_t cbor5_size = cbor_det_size(cbor5, output_size);
  assert (cbor5_size > 0);
  assert (cbor_det_size(cbor5, cbor5_size) == cbor5_size);
  // failure
  assert (cbor_det_size(cbor5, cbor5_size - 1) == 0);

  /* Serialize a CBOR object at offset 0 of the output
     buffer. cbor_det_serialize_safe takes as argument the byte size
     of the output buffer, and returns either 0 if the output buffer
     is too small, or the byte size of the CBOR object written, which
     is a positive integer.
  */
  // success
  uint8_t output[output_size];
  size_t cbor5_serialized_size = cbor_det_serialize_safe(cbor5, output, output_size);
  assert (cbor5_serialized_size == cbor5_size);
  // failure
  #define output_fail_size 2
  uint8_t output_fail[output_fail_size];
  assert (cbor_det_serialize_safe(cbor5, output_fail, output_fail_size) == 0);


  /* 4. Validation and parsing */

  /* Check that an input buffer contains a valid deterministic byte
     encoding of a CBOR object. cbor_det_validate takes an input
     buffer and its length, and returns either 0 if the bytes are
     invalid, or the byte size of the object, which is a positive
     integer. cbor_det_validate uses constant stack and memory
     space.
  */
  // success
  uint8_t validated_size = cbor_det_validate(output, output_size);
  assert (validated_size == cbor5_size);
  // failure: see RFC 8949, Section 3.3
  output_fail[0] = 0xf8u;
  output_fail[1] = 0;
  assert (cbor_det_validate(output_fail, output_fail_size) == 0);

  /* Stack-allocate a CBOR object corresponding to a valid byte
     sequence. cbor_det_parse MUST take the size returned by
     cbor_det_validate, NOT the size of the input.

     cbor_det_parse copies only an integer, a simple value, the tag of
     a tagged object, or the length of an array or map.  Otherwise,
     the resulting CBOR object internally contains pointers to the
     input bytes. Access operations can be used on the resulting CBOR
     object.
  */
  cbor_det_t parsed = cbor_det_parse(output, validated_size);
  assert (cbor_det_major_type(parsed) == CBOR_MAJOR_TYPE_MAP);
  assert (cbor_det_equal(parsed, cbor5));
  assert (cbor_det_get_map_length(parsed) == 2);
  assert (cbor_det_map_get(parsed, cbor0, &value));
  assert (cbor_det_equal(value, cbor1));
  assert (cbor_det_map_get(parsed, cbor2, &value));
  assert (cbor_det_equal(value, cbor3));


  return 0;
}
