module CBOR.SteelST.Type.Def
include CBOR.SteelST.Type.Base
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

inline_for_extraction noextract
val cbor_serialized_payload_t: Type0

noextract [@@erasable; noextract_to "krml"]
val cbor_serialized_footprint_t: Type0

[@@no_auto_projectors]
noeq
type cbor_serialized = {
  cbor_serialized_size: SZ.t;
  cbor_serialized_payload: cbor_serialized_payload_t;
  footprint: cbor_serialized_footprint_t; // ghost
}

noextract [@@erasable; noextract_to "krml"]
val cbor_footprint_t: Type0

val dummy_cbor_footprint: cbor_footprint_t

[@@no_auto_projectors]
noeq
type cbor_tagged0 = {
  cbor_tagged0_tag: U64.t;
  cbor_tagged0_payload: R.ref cbor;
  footprint: Ghost.erased cbor;
}

and cbor_array = {
  cbor_array_length: U64.t;
  cbor_array_payload: A.array cbor;
  footprint: Ghost.erased (Seq.seq cbor);
}

and cbor_map_entry = {
  cbor_map_entry_key: cbor;
  cbor_map_entry_value: cbor;
}

and cbor_map = {
  cbor_map_length: U64.t;
  cbor_map_payload: A.array cbor_map_entry;
  footprint: Ghost.erased (Seq.seq cbor_map_entry);
}

and cbor =
| CBOR_Case_Int64:
  v: cbor_int ->
  self_footprint: cbor_footprint_t ->
  cbor
| CBOR_Case_String:
  v: cbor_string ->
  self_footprint: cbor_footprint_t ->
  permission: perm ->
  cbor
| CBOR_Case_Tagged:
  v: cbor_tagged0 ->
  cbor
| CBOR_Case_Array:
  v: cbor_array ->
  self_footprint: cbor_footprint_t ->
  cbor
| CBOR_Case_Map:
  v: cbor_map ->
  self_footprint: cbor_footprint_t ->
  cbor
| CBOR_Case_Simple_value:
  v: Cbor.simple_value ->
  self_footprint: cbor_footprint_t ->
  cbor
| CBOR_Case_Serialized:
  v: cbor_serialized ->
  self_footprint: cbor_footprint_t ->
  cbor
