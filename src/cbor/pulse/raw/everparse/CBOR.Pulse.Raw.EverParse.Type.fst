module CBOR.Pulse.Raw.EverParse.Type
include CBOR.Pulse.Raw.Util
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module I = LowParse.PulseParse.Iterator

// not reusing raw_uint64, for packing purposes
noeq
type cbor_int = {
  cbor_int_type: major_type_uint64_or_neg_int64;
  cbor_int_size: integer_size;
  cbor_int_value: (value: U64.t { raw_uint64_size_prop cbor_int_size value });
}

// not reusing raw_uint64, for packing purposes
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

noeq
type cbor_tagged ([@@@strictly_positive] cbor_raw: Type0) = {
  cbor_tagged_tag: raw_uint64;
  cbor_tagged_ptr: ref cbor_raw;
  cbor_tagged_ref_perm: perm;
//  cbor_tagged_payload_perm: perm;
}

noeq
type cbor_array ([@@@strictly_positive] cbor_raw: Type0) = {
  cbor_array_length_size: integer_size;
  cbor_array_ptr: (ar: I.iterator cbor_raw { let len = SZ.v (I.iterator_length ar) in
    FStar.UInt.fits len 64 /\
    raw_uint64_size_prop cbor_array_length_size (U64.uint_to_t len)
  });
  cbor_array_slice_perm: perm;
//  cbor_array_payload_perm: perm;
}

noeq
type cbor_map_entry ([@@@strictly_positive] cbor_raw: Type0) = {
  cbor_map_entry_key: cbor_raw;
  cbor_map_entry_value: cbor_raw;
}

noeq
type cbor_map ([@@@strictly_positive] cbor_raw: Type0) = {
  cbor_map_length_size: integer_size;
  cbor_map_ptr: (ar: I.iterator (cbor_map_entry cbor_raw) { let len = SZ.v (I.iterator_length ar) in
    FStar.UInt.fits len 64 /\
    raw_uint64_size_prop cbor_map_length_size (U64.uint_to_t len)
  });
  cbor_map_slice_perm: perm;
//  cbor_map_payload_perm: perm;
}

noeq
type cbor_raw =
| CBOR_Case_Invalid
| CBOR_Case_Int: v: cbor_int -> cbor_raw
| CBOR_Case_Simple: v: simple_value -> cbor_raw
| CBOR_Case_String: v: cbor_string -> cbor_raw
| CBOR_Case_Tagged: v: cbor_tagged cbor_raw -> cbor_raw
| CBOR_Case_Array: v: cbor_array cbor_raw -> cbor_raw
| CBOR_Case_Map: v: cbor_map cbor_raw -> cbor_raw
