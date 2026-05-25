

#ifndef CBORDet_H
#define CBORDet_H

#if defined(__cplusplus)
extern "C" {
#endif

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

typedef struct cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_tagged_tag;
  cbor_raw *cbor_tagged_ptr;
}
cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct cbor_tagged_serialized_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_tagged_serialized_tag;
  Pulse_Lib_Slice_slice__uint8_t cbor_tagged_serialized_ptr;
}
cbor_tagged_serialized;

typedef struct Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  cbor_raw *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

#define LowParse_PulseParse_Iterator_Type_Empty 0
#define LowParse_PulseParse_Iterator_Type_Singleton 1
#define LowParse_PulseParse_Iterator_Type_Slice 2
#define LowParse_PulseParse_Iterator_Type_Serialized 3

typedef uint8_t
LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags;

typedef struct
LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags
  tag;
  union {
    cbor_raw *case_Singleton;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_raw case_Slice;
    struct
    {
      size_t count;
      Pulse_Lib_Slice_slice__uint8_t payload;
    }
    case_Serialized;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

#define LowParse_PulseParse_Iterator_Type_Base 0
#define LowParse_PulseParse_Iterator_Type_Append 1

typedef uint8_t
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags;

typedef struct
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags tag;
  union {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    case_Base;
    struct
    {
      size_t cb;
      size_t ca;
      size_t ob;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *before;
      size_t oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *after;
    }
    case_Append;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  uint8_t cbor_array_length_size;
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  cbor_array_ptr;
}
cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct
LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags
  tag;
  union {
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *case_Singleton;
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    case_Slice;
    struct
    {
      size_t count;
      Pulse_Lib_Slice_slice__uint8_t payload;
    }
    case_Serialized;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags tag;
  union {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    case_Base;
    struct
    {
      size_t cb;
      size_t ca;
      size_t ob;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *before;
      size_t oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      *after;
    }
    case_Append;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  uint8_t cbor_map_length_size;
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  cbor_map_ptr;
}
cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

#define CBOR_Case_Invalid 0
#define CBOR_Case_Int 1
#define CBOR_Case_Simple 2
#define CBOR_Case_String 3
#define CBOR_Case_Tagged 4
#define CBOR_Case_Tagged_Serialized 5
#define CBOR_Case_Array 6
#define CBOR_Case_Map 7

typedef uint8_t cbor_raw_tags;

typedef struct cbor_raw_s
{
  cbor_raw_tags tag;
  union {
    cbor_int case_CBOR_Case_Int;
    uint8_t case_CBOR_Case_Simple;
    cbor_string case_CBOR_Case_String;
    cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw case_CBOR_Case_Tagged;
    cbor_tagged_serialized case_CBOR_Case_Tagged_Serialized;
    cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw case_CBOR_Case_Array;
    cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw case_CBOR_Case_Map;
  }
  ;
}
cbor_raw;

typedef struct
LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  before;
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw after;
}
LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct
LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  before;
  LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  after;
}
LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef struct cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  cbor_raw cbor_map_entry_key;
  cbor_raw cbor_map_entry_value;
}
cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

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

bool uu___is_CBOR_Case_Invalid(cbor_raw projectee);

bool uu___is_CBOR_Case_Int(cbor_raw projectee);

bool uu___is_CBOR_Case_Simple(cbor_raw projectee);

bool uu___is_CBOR_Case_String(cbor_raw projectee);

bool uu___is_CBOR_Case_Tagged(cbor_raw projectee);

bool uu___is_CBOR_Case_Tagged_Serialized(cbor_raw projectee);

bool uu___is_CBOR_Case_Array(cbor_raw projectee);

bool uu___is_CBOR_Case_Map(cbor_raw projectee);

typedef cbor_raw cbor_det_t;

typedef cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw cbor_det_map_entry_t;

typedef LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_array_iterator_t;

typedef LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_map_iterator_t;

cbor_raw dummy_cbor_det_t(void);

cbor_raw cbor_det_reset_perm(cbor_raw x);

size_t cbor_det_validate(uint8_t *input, size_t input_len);

cbor_raw cbor_det_parse(uint8_t *input, size_t len);

size_t cbor_det_size(cbor_raw x, size_t bound);

size_t cbor_det_serialize(cbor_raw x, uint8_t *output, size_t output_len);

size_t cbor_det_serialize_safe(cbor_raw x, uint8_t *output, size_t output_len);

bool cbor_det_impl_utf8_correct_from_array(uint8_t *s, size_t len);

cbor_raw cbor_det_mk_simple_value(uint8_t v);

cbor_raw cbor_det_mk_int64(uint8_t ty, uint64_t v);

cbor_raw cbor_det_mk_tagged(uint64_t tag, cbor_raw *r);

bool cbor_det_mk_byte_string_from_arrayptr(uint8_t *a, uint64_t len, cbor_raw *dest);

bool cbor_det_mk_text_string_from_arrayptr(uint8_t *a, uint64_t len, cbor_raw *dest);

cbor_raw cbor_det_mk_array_from_array(cbor_raw *a, uint64_t len);

cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_mk_map_entry(cbor_raw xk, cbor_raw xv);

cbor_raw
cbor_det_mk_map_from_array(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  uint64_t len
);

bool
cbor_det_mk_map_from_array_safe(
  cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *a,
  uint64_t len,
  cbor_raw *dest
);

bool cbor_det_equal(cbor_raw x1, cbor_raw x2);

uint8_t cbor_det_major_type(cbor_raw x);

uint8_t cbor_det_read_simple_value(cbor_raw x);

uint64_t cbor_det_read_uint64(cbor_raw x);

uint64_t cbor_det_get_string_length(cbor_raw x);

uint64_t cbor_det_get_tagged_tag(cbor_raw x);

cbor_raw cbor_det_get_tagged_payload(cbor_raw x);

uint8_t *cbor_det_get_string(cbor_raw x);

uint64_t cbor_det_get_array_length(cbor_raw x);

LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_array_iterator_start(cbor_raw x);

bool
cbor_det_array_iterator_is_empty(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
);

uint64_t
cbor_det_array_iterator_length(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x
);

cbor_raw
cbor_det_array_iterator_next(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw *x
);

LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_array_iterator_truncate(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw x,
  uint64_t len
);

cbor_raw cbor_det_get_array_item(cbor_raw x, uint64_t i);

uint64_t cbor_det_get_map_length(cbor_raw x);

LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_map_iterator_start(cbor_raw x);

bool
cbor_det_map_iterator_is_empty(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  x
);

cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_det_map_iterator_next(
  LowParse_PulseParse_Iterator_Type_iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
  *x
);

cbor_raw cbor_det_map_entry_key(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e);

cbor_raw cbor_det_map_entry_value(cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw e);

bool cbor_det_map_get(cbor_raw x, cbor_raw k, cbor_raw *dest);

size_t cbor_det_serialize_tag_to_array(uint64_t tag, uint8_t *out, size_t out_len);

size_t
cbor_det_serialize_array_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off);

size_t
cbor_det_serialize_string_to_array(uint8_t ty, uint64_t off, uint8_t *out, size_t out_len);

bool
cbor_det_serialize_map_insert_to_array(uint8_t *out, size_t out_len, size_t off2, size_t off3);

size_t cbor_det_serialize_map_to_array(uint64_t len, uint8_t *out, size_t out_len, size_t off);

typedef struct cbor_det_freeable_t__s
{
  cbor_raw cbor;
  uint8_t *buf;
  size_t len;
}
cbor_det_freeable_t_;

typedef cbor_det_freeable_t_ cbor_det_freeable_t;

cbor_raw cbor_get_from_freeable(cbor_det_freeable_t_ r);

cbor_det_freeable_t_ cbor_copy(cbor_raw c);

void cbor_free(cbor_det_freeable_t_ x);

#if defined(__cplusplus)
}
#endif

#define CBORDet_H_DEFINED
#endif /* CBORDet_H */
