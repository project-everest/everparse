module CBOR.Pulse.Raw.Type
include CBOR.Pulse.Raw.Util
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64

inline_for_extraction
noeq
type cbor_serialized = {
  cbor_serialized_header: raw_uint64;
  cbor_serialized_payload: slice U8.t;
  cbor_serialized_perm: perm;
}

// not reusing raw_uint64, for packing purposes
inline_for_extraction
noeq
type cbor_int = {
  cbor_int_type: major_type_uint64_or_neg_int64;
  cbor_int_size: integer_size;
  cbor_int_value: (value: U64.t { raw_uint64_size_prop cbor_int_size value });
}

// not reusing raw_uint64, for packing purposes
inline_for_extraction
noeq
type cbor_string = {
  cbor_string_type: major_type_byte_string_or_text_string;
  cbor_string_size: integer_size;
  cbor_string_ptr: (ptr: slice U8.t {
    let len = SZ.v (len ptr) in
    FStar.UInt.fits len 64 /\
    raw_uint64_size_prop cbor_string_size (U64.uint_to_t len)
  }) ;
  cbor_string_perm: perm;
}

[@@no_auto_projectors]
noeq
type cbor_tagged = {
  cbor_tagged_tag: raw_uint64;
  cbor_tagged_ptr: ref cbor_raw;
  cbor_tagged_ref_perm: perm;
  cbor_tagged_payload_perm: perm;
}

and cbor_array = {
  cbor_array_length_size: integer_size;
  cbor_array_ptr: (ar: slice cbor_raw { let len = SZ.v (len ar) in
    FStar.UInt.fits len 64 /\
    raw_uint64_size_prop cbor_array_length_size (U64.uint_to_t len)
  });
  cbor_array_array_perm: perm;
  cbor_array_payload_perm: perm;
}

and cbor_map_entry = {
  cbor_map_entry_key: cbor_raw;
  cbor_map_entry_value: cbor_raw;
}

and cbor_map = {
  cbor_map_length_size: integer_size;
  cbor_map_ptr: (ar: slice cbor_map_entry { let len = SZ.v (len ar) in
    FStar.UInt.fits len 64 /\
    raw_uint64_size_prop cbor_map_length_size (U64.uint_to_t len)
  });
  cbor_map_array_perm: perm;
  cbor_map_payload_perm: perm;
}

and cbor_raw =
| CBOR_Case_Int: v: cbor_int -> cbor_raw
| CBOR_Case_Simple: v: simple_value -> cbor_raw
| CBOR_Case_String: v: cbor_string -> cbor_raw
| CBOR_Case_Tagged: v: cbor_tagged -> cbor_raw
| CBOR_Case_Array: v: cbor_array -> cbor_raw
| CBOR_Case_Map: v: cbor_map -> cbor_raw
| CBOR_Case_Serialized_Tagged: v: cbor_serialized -> cbor_raw
| CBOR_Case_Serialized_Array: v: cbor_serialized -> cbor_raw
| CBOR_Case_Serialized_Map: v: cbor_serialized -> cbor_raw

let cbor_array_iterator
= CBOR.Pulse.Raw.Iterator.cbor_raw_iterator cbor_raw

let cbor_map_iterator
= CBOR.Pulse.Raw.Iterator.cbor_raw_iterator cbor_map_entry
