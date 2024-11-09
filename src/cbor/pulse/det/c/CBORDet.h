

#ifndef __CBORDet_H
#define __CBORDet_H

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

typedef struct cbor_raw_s cbor_raw;

typedef struct Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  cbor_raw *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct cbor_map_entry_s cbor_map_entry;

typedef struct Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  cbor_map_entry *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry;

typedef struct cbor_int_s
{
  uint8_t cbor_int_type;
  uint8_t cbor_int_size;
  uint64_t cbor_int_value;
}
cbor_int;

typedef struct cbor_string_s
{
  uint8_t cbor_string_type;
  uint8_t cbor_string_size;
  Pulse_Lib_Slice_slice__uint8_t cbor_string_ptr;
}
cbor_string;

typedef struct cbor_raw_s cbor_raw;

typedef struct cbor_tagged_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_tagged_tag;
  cbor_raw *cbor_tagged_ptr;
}
cbor_tagged;

typedef struct cbor_array_s
{
  uint8_t cbor_array_length_size;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw cbor_array_ptr;
}
cbor_array;

typedef struct cbor_map_s
{
  uint8_t cbor_map_length_size;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry cbor_map_ptr;
}
cbor_map;

typedef struct cbor_serialized_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_serialized_header;
  Pulse_Lib_Slice_slice__uint8_t cbor_serialized_payload;
}
cbor_serialized;

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

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t
FStar_Pervasives_Native_option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_tags;

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
    Pulse_Lib_Slice_slice__uint8_t case_CBOR_Raw_Iterator_Serialized;
  }
  ;
}
CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  union {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry case_CBOR_Raw_Iterator_Slice;
    Pulse_Lib_Slice_slice__uint8_t case_CBOR_Raw_Iterator_Serialized;
  }
  ;
}
CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;

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

bool uu___is_CBOR_Case_Int(cbor_raw projectee);

bool uu___is_CBOR_Case_Simple(cbor_raw projectee);

bool uu___is_CBOR_Case_String(cbor_raw projectee);

bool uu___is_CBOR_Case_Tagged(cbor_raw projectee);

bool uu___is_CBOR_Case_Array(cbor_raw projectee);

bool uu___is_CBOR_Case_Map(cbor_raw projectee);

bool uu___is_CBOR_Case_Serialized_Tagged(cbor_raw projectee);

bool uu___is_CBOR_Case_Serialized_Array(cbor_raw projectee);

bool uu___is_CBOR_Case_Serialized_Map(cbor_raw projectee);

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

size_t cbor_det_validate(Pulse_Lib_Slice_slice__uint8_t input);

cbor_raw cbor_det_parse(Pulse_Lib_Slice_slice__uint8_t input, size_t len);

size_t cbor_det_size(cbor_raw x, size_t bound);

size_t cbor_det_serialize(cbor_raw x, Pulse_Lib_Slice_slice__uint8_t output);

cbor_raw cbor_det_mk_simple_value(uint8_t v);

cbor_raw cbor_det_mk_int64(uint8_t ty, uint64_t v);

cbor_raw cbor_det_mk_string(uint8_t ty, Pulse_Lib_Slice_slice__uint8_t s);

cbor_raw cbor_det_mk_tagged(uint64_t tag, cbor_raw *r);

cbor_raw cbor_det_mk_array(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw a);

cbor_raw cbor_det_mk_map(Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry a);

bool cbor_det_equal(cbor_raw x1, cbor_raw x2);

uint8_t cbor_det_major_type(cbor_raw x);

uint8_t cbor_det_read_simple_value(cbor_raw x);

uint64_t cbor_det_read_uint64(cbor_raw x);

Pulse_Lib_Slice_slice__uint8_t cbor_det_get_string(cbor_raw x);

uint64_t cbor_det_get_tagged_tag(cbor_raw x);

cbor_raw cbor_det_get_tagged_payload(cbor_raw x);

uint64_t cbor_det_get_array_length(cbor_raw x);

CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_iterator_start(cbor_raw x);

bool
cbor_det_array_iterator_is_empty(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw x
);

cbor_raw
cbor_det_array_iterator_next(
  CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw *x
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

typedef struct FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  FStar_Pervasives_Native_option__LowParse_Pulse_Base_with_perm_Pulse_Lib_Slice_slice_CBOR_Pulse_Raw_Type_cbor_raw_tags
  tag;
  cbor_raw v;
}
FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw;

FStar_Pervasives_Native_option__CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_map_get(cbor_raw x, cbor_raw k);

cbor_raw cbor_det_mk_string_from_array(uint8_t ty, uint8_t *a, uint64_t len);

cbor_raw cbor_det_mk_array_from_array(cbor_raw *a, uint64_t len);

cbor_raw cbor_det_mk_map_from_array(cbor_map_entry *a, uint64_t len);


#define __CBORDet_H_DEFINED
#endif
