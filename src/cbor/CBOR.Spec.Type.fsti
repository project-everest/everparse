module CBOR.Spec.Type
include CBOR.Spec.Constants

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* Simple values *)

[@@CMacro]
let min_simple_value_long_argument = 32uy

[@@CMacro]
let max_simple_value_additional_info = 23uy

inline_for_extraction
noextract
let simple_value_wf
  (x: U8.t)
: Tot bool
= x `U8.lte` max_simple_value_additional_info || min_simple_value_long_argument `U8.lte` x

inline_for_extraction
noextract
let simple_value : eqtype =
  (x: U8.t { simple_value_wf x == true } )

(* Raw data items, disregarding ordering of map entries *)

noextract
noeq
type raw_data_item
= | Simple: (v: simple_value) -> raw_data_item
  | Int64: (typ: major_type_uint64_or_neg_int64) -> (v: U64.t) -> raw_data_item
  | String: (typ: major_type_byte_string_or_text_string) -> (v: Seq.seq U8.t { FStar.UInt.fits (Seq.length v) U64.n }) -> raw_data_item // Section 3.1: "a string containing an invalid UTF-8 sequence is well-formed but invalid", so we don't care about UTF-8 specifics here.
  | Array: (v: list raw_data_item { FStar.UInt.fits (List.Tot.length v) U64.n }) -> raw_data_item
  | Map: (v: list (raw_data_item & raw_data_item) { FStar.UInt.fits (List.Tot.length v) U64.n }) -> raw_data_item
  | Tagged: (tag: U64.t) -> (v: raw_data_item) -> raw_data_item
//  | Float: (v: Float.float) -> raw_data_item // TODO

noextract
let get_major_type
  (d: raw_data_item)
: Tot major_type_t
= match d with
  | Simple _ -> major_type_simple_value
  | Int64 m _ -> m
  | String m _ -> m
  | Array _ -> major_type_array
  | Map _ -> major_type_map
  | Tagged _ _ -> major_type_tagged
