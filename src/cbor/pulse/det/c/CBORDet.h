

#ifndef CBORDet_H
#define CBORDet_H

#include "krmllib.h"

typedef struct CBOR_Spec_Raw_Base_raw_uint64_s
{
  uint8_t size;
  uint64_t value;
}
CBOR_Spec_Raw_Base_raw_uint64;

typedef struct Pulse_Lib_Slice_slice__uint8_t_s
{
  uint8_t *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__uint8_t;

typedef struct CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator_s
{
  Pulse_Lib_Slice_slice__uint8_t s;
  uint64_t len;
}
CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator;

typedef struct cbor_string_s
{
  uint8_t cbor_string_type;
  uint8_t cbor_string_size;
  Pulse_Lib_Slice_slice__uint8_t cbor_string_ptr;
}
cbor_string;

typedef struct cbor_serialized_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_serialized_header;
  Pulse_Lib_Slice_slice__uint8_t cbor_serialized_payload;
}
cbor_serialized;

typedef struct cbor_raw_s cbor_raw;

typedef struct cbor_tagged_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_tagged_tag;
  cbor_raw *cbor_tagged_ptr;
}
cbor_tagged;

typedef struct cbor_raw_s cbor_raw;

typedef struct cbor_raw_s cbor_raw;

typedef struct Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  cbor_raw *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct cbor_array_s
{
  uint8_t cbor_array_length_size;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw cbor_array_ptr;
}
cbor_array;

typedef struct cbor_map_entry_s cbor_map_entry;

typedef struct Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  cbor_map_entry *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry;

typedef struct cbor_map_s
{
  uint8_t cbor_map_length_size;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry cbor_map_ptr;
}
cbor_map;

typedef struct cbor_int_s
{
  uint8_t cbor_int_type;
  uint8_t cbor_int_size;
  uint64_t cbor_int_value;
}
cbor_int;

#define CBOR_Case_Int 0
#define CBOR_Case_Simple 1
#define CBOR_Case_String 2
#define CBOR_Case_Tagged 3
#define CBOR_Case_Array 4
#define CBOR_Case_Map 5
#define CBOR_Case_Serialized_Tagged 6
#define CBOR_Case_Serialized_Array 7
#define CBOR_Case_Serialized_Map 8

typedef uint8_t cbor_raw_tags;

typedef struct cbor_raw_s
{
  cbor_raw_tags tag;
  union {
    cbor_int case_CBOR_Case_Int;
    uint8_t case_CBOR_Case_Simple;
    cbor_string case_CBOR_Case_String;
    cbor_tagged case_CBOR_Case_Tagged;
    cbor_array case_CBOR_Case_Array;
    cbor_map case_CBOR_Case_Map;
    cbor_serialized case_CBOR_Case_Serialized_Tagged;
    cbor_serialized case_CBOR_Case_Serialized_Array;
    cbor_serialized case_CBOR_Case_Serialized_Map;
  }
  ;
}
cbor_raw;

typedef struct cbor_map_entry_s
{
  cbor_raw cbor_map_entry_key;
  cbor_raw cbor_map_entry_value;
}
cbor_map_entry;

#define CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Slice 0
#define CBOR_Pulse_Raw_Iterator_CBOR_Raw_Iterator_Serialized 1

typedef uint8_t CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_tags;

typedef struct CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  union {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw case_CBOR_Raw_Iterator_Slice;
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator case_CBOR_Raw_Iterator_Serialized;
  }
  ;
}
CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  union {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry case_CBOR_Raw_Iterator_Slice;
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator case_CBOR_Raw_Iterator_Serialized;
  }
  ;
}
CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;

typedef struct cbor_freeable0_s cbor_freeable0;

typedef struct cbor_freeable_box_s
{
  cbor_raw *box_cbor;
  cbor_freeable0 *box_footprint;
}
cbor_freeable_box;

typedef struct cbor_freeable0_s cbor_freeable0;

typedef struct cbor_freeable_array_s
{
  cbor_raw *array_cbor;
  cbor_freeable0 *array_footprint;
  size_t array_len;
}
cbor_freeable_array;

typedef struct cbor_freeable_map_entry_s cbor_freeable_map_entry;

typedef struct cbor_freeable_map_s
{
  cbor_map_entry *map_cbor;
  cbor_freeable_map_entry *map_footprint;
  size_t map_len;
}
cbor_freeable_map;

#define CBOR_Copy_Bytes 0
#define CBOR_Copy_Box 1
#define CBOR_Copy_Array 2
#define CBOR_Copy_Map 3
#define CBOR_Copy_Unit 4

typedef uint8_t cbor_freeable0_tags;

typedef struct cbor_freeable0_s
{
  cbor_freeable0_tags tag;
  union {
    uint8_t *case_CBOR_Copy_Bytes;
    cbor_freeable_box case_CBOR_Copy_Box;
    cbor_freeable_array case_CBOR_Copy_Array;
    cbor_freeable_map case_CBOR_Copy_Map;
  }
  ;
}
cbor_freeable0;

typedef struct cbor_freeable_map_entry_s
{
  cbor_freeable0 map_entry_key;
  cbor_freeable0 map_entry_value;
}
cbor_freeable_map_entry;

typedef struct cbor_freeable_s
{
  cbor_raw cbor;
  cbor_freeable0 footprint;
}
cbor_freeable;

#define CBOR_MAJOR_TYPE_SIMPLE_VALUE (7U)

#define CBOR_MAJOR_TYPE_UINT64 (0U)

#define CBOR_MAJOR_TYPE_NEG_INT64 (1U)

#define CBOR_MAJOR_TYPE_BYTE_STRING (2U)

#define CBOR_MAJOR_TYPE_TEXT_STRING (3U)

#define CBOR_MAJOR_TYPE_ARRAY (4U)

#define CBOR_MAJOR_TYPE_MAP (5U)

#define CBOR_MAJOR_TYPE_TAGGED (6U)

#define MIN_SIMPLE_VALUE_LONG_ARGUMENT (32U)

#define MAX_SIMPLE_VALUE_ADDITIONAL_INFO (23U)

typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_array_iterator;

typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_map_iterator;

typedef cbor_raw cbor_det_t;

typedef cbor_map_entry cbor_det_map_entry_t;

typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_t;

typedef CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_det_map_iterator_t;

cbor_raw dummy_cbor_det_t(void);

cbor_raw cbor_det_reset_perm(cbor_raw x1);

size_t cbor_det_validate(uint8_t *input, size_t input_len);

cbor_raw cbor_det_parse(uint8_t *input, size_t len);

size_t cbor_det_size(cbor_raw x, size_t bound);

size_t cbor_det_serialize(cbor_raw x, uint8_t *output, size_t output_len);

size_t cbor_det_serialize_safe(cbor_raw x, uint8_t *output, size_t output_len);

bool cbor_det_impl_utf8_correct_from_array(uint8_t *s, size_t len);

cbor_raw cbor_det_mk_simple_value(uint8_t v);

cbor_raw cbor_det_mk_int64(uint8_t ty, uint64_t v);

cbor_raw cbor_det_mk_tagged(uint64_t tag, cbor_raw *r);

cbor_raw cbor_det_mk_string_from_arrayptr(uint8_t ty, uint8_t *a, uint64_t len);

cbor_raw cbor_det_mk_array_from_array(cbor_raw *a, uint64_t len);

cbor_map_entry cbor_det_mk_map_entry(cbor_raw xk, cbor_raw xv);

cbor_raw cbor_det_mk_map_from_array(cbor_map_entry *a, uint64_t len);

bool cbor_det_mk_map_from_array_safe(cbor_map_entry *a, uint64_t len, cbor_raw *dest);

bool cbor_det_equal(cbor_raw x1, cbor_raw x2);

uint8_t cbor_det_major_type(cbor_raw x);

uint8_t cbor_det_read_simple_value(cbor_raw x);

uint64_t cbor_det_read_uint64(cbor_raw x);

uint64_t cbor_det_get_string_length(cbor_raw x);

uint64_t cbor_det_get_tagged_tag(cbor_raw x);

cbor_raw cbor_det_get_tagged_payload(cbor_raw x);

uint8_t *cbor_det_get_string(cbor_raw x);

uint64_t cbor_det_get_array_length(cbor_raw x);

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_start(cbor_raw x);

bool
cbor_det_array_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x
);

uint64_t
cbor_det_array_iterator_length(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x
);

cbor_raw
cbor_det_array_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw *x
);

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_truncate(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x,
  uint64_t len
);

cbor_raw cbor_det_get_array_item(cbor_raw x, uint64_t i);

uint64_t cbor_det_get_map_length(cbor_raw x);

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_det_map_iterator_start(cbor_raw x);

bool
cbor_det_map_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry x
);

cbor_map_entry
cbor_det_map_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry *x
);

cbor_raw cbor_det_map_entry_key(cbor_map_entry x2);

cbor_raw cbor_det_map_entry_value(cbor_map_entry x2);

bool cbor_det_map_get(cbor_raw x, cbor_raw k, cbor_raw *dest);

size_t cbor_det_serialize_tag_to_array(uint64_t tag, uint8_t *out, size_t out_len);

size_t
cbor_det_serialize_array_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off);

size_t
cbor_det_serialize_string_to_array(uint8_t ty, uint64_t off, uint8_t *out, size_t out_len);

bool
cbor_det_serialize_map_insert_to_array(uint8_t *out, size_t out_len, size_t off2, size_t off3);

size_t cbor_det_serialize_map_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off);

typedef cbor_freeable cbor_det_freeable_t;

cbor_raw cbor_get_from_freeable(cbor_freeable x);

cbor_freeable cbor_copy(cbor_raw c);

void cbor_free(cbor_freeable x);


#define CBORDet_H_DEFINED
#endif /* CBORDet_H */
