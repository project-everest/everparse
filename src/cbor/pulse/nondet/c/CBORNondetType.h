

#ifndef CBORNondetType_H
#define CBORNondetType_H

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

typedef struct byte_slice_s
{
  uint8_t *elt;
  size_t len;
}
byte_slice;

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
  byte_slice cbor_string_ptr;
}
cbor_string;

typedef struct cbor_tagged_serialized_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_tagged_serialized_tag;
  byte_slice cbor_tagged_serialized_ptr;
}
cbor_tagged_serialized;

typedef struct cbor_raw_s cbor_raw;

typedef struct cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_tagged_tag;
  cbor_raw *cbor_tagged_ptr;
}
cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

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
      byte_slice payload;
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
      byte_slice payload;
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

typedef cbor_raw cbor_nondet_t;

#define IBase 0
#define IPair 1

typedef uint8_t cbor_nondet_array_iterator_t_tags;

typedef struct cbor_nondet_array_iterator_t_s
{
  cbor_nondet_array_iterator_t_tags tag;
  union {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    case_IBase;
    struct
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      before;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw after;
    }
    case_IPair;
  }
  ;
}
cbor_nondet_array_iterator_t;

typedef struct cbor_nondet_map_iterator_t_s
{
  cbor_nondet_array_iterator_t_tags tag;
  union {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    case_IBase;
    struct
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      before;
      LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
      after;
    }
    case_IPair;
  }
  ;
}
cbor_nondet_map_iterator_t;

typedef struct cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_s
{
  cbor_raw cbor_map_entry_key;
  cbor_raw cbor_map_entry_value;
}
cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;

typedef cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw cbor_nondet_map_entry_t;

typedef LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_nondet_array_append_cell_t;

typedef LowParse_PulseParse_Iterator_Type_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
cbor_nondet_map_entry_insert_cell_t;

#if defined(__cplusplus)
}
#endif

#define CBORNondetType_H_DEFINED
#endif /* CBORNondetType_H */
