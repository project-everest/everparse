/*
   Copyright 2023, 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/


#ifndef __CBOR_H
#define __CBOR_H

#include "krmllib.h"

#define CBOR_MAJOR_TYPE_SIMPLE_VALUE (7U)

#define CBOR_MAJOR_TYPE_UINT64 (0U)

#define CBOR_MAJOR_TYPE_NEG_INT64 (1U)

#define CBOR_MAJOR_TYPE_BYTE_STRING (2U)

#define CBOR_MAJOR_TYPE_TEXT_STRING (3U)

#define CBOR_MAJOR_TYPE_ARRAY (4U)

#define CBOR_MAJOR_TYPE_MAP (5U)

#define CBOR_MAJOR_TYPE_TAGGED (6U)

typedef struct cbor_int_s
{
  uint8_t cbor_int_type;
  uint64_t cbor_int_value;
}
cbor_int;

typedef struct cbor_string_s
{
  uint8_t cbor_string_type;
  uint64_t cbor_string_length;
  uint8_t *cbor_string_payload;
}
cbor_string;

typedef struct cbor_serialized_s
{
  size_t cbor_serialized_size;
  uint8_t *cbor_serialized_payload;
}
cbor_serialized;

typedef struct cbor_s cbor;

typedef struct cbor_s cbor;

typedef struct cbor_tagged0_s
{
  uint64_t cbor_tagged0_tag;
  cbor *cbor_tagged0_payload;
}
cbor_tagged0;

typedef struct cbor_s cbor;

typedef struct cbor_s cbor;

typedef struct cbor_array_s
{
  uint64_t cbor_array_length;
  cbor *cbor_array_payload;
}
cbor_array;

typedef struct cbor_map_entry_s cbor_map_entry;

typedef struct cbor_map_s
{
  uint64_t cbor_map_length;
  cbor_map_entry *cbor_map_payload;
}
cbor_map;

#define CBOR_Case_Int64 0
#define CBOR_Case_String 1
#define CBOR_Case_Tagged 2
#define CBOR_Case_Array 3
#define CBOR_Case_Map 4
#define CBOR_Case_Simple_value 5
#define CBOR_Case_Serialized 6

typedef uint8_t cbor_tags;

typedef struct cbor_s
{
  cbor_tags tag;
  union {
    cbor_int case_CBOR_Case_Int64;
    cbor_string case_CBOR_Case_String;
    cbor_tagged0 case_CBOR_Case_Tagged;
    cbor_array case_CBOR_Case_Array;
    cbor_map case_CBOR_Case_Map;
    uint8_t case_CBOR_Case_Simple_value;
    cbor_serialized case_CBOR_Case_Serialized;
  }
  ;
}
cbor;

typedef struct cbor_map_entry_s
{
  cbor cbor_map_entry_key;
  cbor cbor_map_entry_value;
}
cbor_map_entry;

#define CBOR_Array_Iterator_Payload_Array 0
#define CBOR_Array_Iterator_Payload_Serialized 1

typedef uint8_t cbor_array_iterator_payload_t_tags;

typedef struct cbor_array_iterator_payload_t_s
{
  cbor_array_iterator_payload_t_tags tag;
  union {
    cbor *case_CBOR_Array_Iterator_Payload_Array;
    uint8_t *case_CBOR_Array_Iterator_Payload_Serialized;
  }
  ;
}
cbor_array_iterator_payload_t;

typedef struct cbor_array_iterator_t_s
{
  uint64_t cbor_array_iterator_length;
  cbor_array_iterator_payload_t cbor_array_iterator_payload;
}
cbor_array_iterator_t;

#define CBOR_Map_Iterator_Payload_Map 0
#define CBOR_Map_Iterator_Payload_Serialized 1

typedef uint8_t cbor_map_iterator_payload_t_tags;

typedef struct cbor_map_iterator_payload_t_s
{
  cbor_map_iterator_payload_t_tags tag;
  union {
    cbor_map_entry *case_CBOR_Map_Iterator_Payload_Map;
    uint8_t *case_CBOR_Map_Iterator_Payload_Serialized;
  }
  ;
}
cbor_map_iterator_payload_t;

typedef struct cbor_map_iterator_t_s
{
  uint64_t cbor_map_iterator_length;
  cbor_map_iterator_payload_t cbor_map_iterator_payload;
}
cbor_map_iterator_t;

extern cbor cbor_dummy;

extern cbor cbor_map_entry_key(cbor_map_entry uu___);

extern cbor cbor_map_entry_value(cbor_map_entry uu___);

extern cbor_map_entry cbor_mk_map_entry(cbor key, cbor value);

typedef struct cbor_read_t_s
{
  bool cbor_read_is_success;
  cbor cbor_read_payload;
  uint8_t *cbor_read_remainder;
  size_t cbor_read_remainder_length;
}
cbor_read_t;

extern cbor_read_t cbor_read(uint8_t *a, size_t sz);

extern cbor_read_t cbor_read_deterministically_encoded(uint8_t *a, size_t sz);

extern cbor_int cbor_destr_int64(cbor c);

extern cbor cbor_constr_int64(uint8_t ty, uint64_t value);

extern uint8_t cbor_destr_simple_value(cbor c);

extern cbor cbor_constr_simple_value(uint8_t value);

extern cbor_string cbor_destr_string(cbor c);

extern cbor cbor_constr_string(uint8_t typ, uint8_t *a, uint64_t len);

extern cbor cbor_constr_array(cbor *a, uint64_t len);

extern uint64_t cbor_array_length(cbor a);

extern cbor cbor_array_index(cbor a, size_t i);

extern cbor_array_iterator_t cbor_dummy_array_iterator;

extern cbor_array_iterator_t cbor_array_iterator_init(cbor a);

extern bool cbor_array_iterator_is_done(cbor_array_iterator_t i);

extern cbor cbor_array_iterator_next(cbor_array_iterator_t *pi);

extern cbor *cbor_read_array(cbor a, cbor *dest, uint64_t len);

typedef struct cbor_tagged_s
{
  uint64_t cbor_tagged_tag;
  cbor cbor_tagged_payload;
}
cbor_tagged;

extern cbor_tagged cbor_destr_tagged(cbor a);

extern cbor cbor_constr_tagged(uint64_t tag, cbor *a);

extern cbor cbor_constr_map(cbor_map_entry *a, uint64_t len);

extern uint64_t cbor_map_length(cbor a);

extern cbor_map_iterator_t cbor_dummy_map_iterator;

extern cbor_map_iterator_t cbor_map_iterator_init(cbor a);

extern bool cbor_map_iterator_is_done(cbor_map_iterator_t i);

extern cbor_map_entry cbor_map_iterator_next(cbor_map_iterator_t *pi);

extern uint8_t cbor_get_major_type(cbor a);

extern int16_t cbor_compare_aux(cbor c1, cbor c2);

extern size_t cbor_write(cbor c, uint8_t *out, size_t sz);


#define __CBOR_H_DEFINED
#endif
