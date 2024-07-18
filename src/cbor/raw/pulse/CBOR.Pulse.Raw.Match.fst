module CBOR.Pulse.Raw.Match
include CBOR.Pulse.Raw.Match.Serialized
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64

let cbor_match_int
  (c: cbor_int)
  (r: raw_data_item)
: Tot vprop
= pure (
    r == Int64 c.cbor_int_type ({ size = c.cbor_int_size; value = c.cbor_int_value })
  )

let cbor_match_simple
  (c: simple_value)
  (r: raw_data_item)
: Tot vprop
= pure (
    r == Simple c
  )

let cbor_match_string
  (c: cbor_string)
  (p: perm)
  (r: raw_data_item)
: Tot vprop
= exists* v . S.pts_to c.cbor_string_ptr #(p `perm_mul` c.cbor_string_perm) v ** pure
    (r == String c.cbor_string_type ({ size = c.cbor_string_size; value = U64.uint_to_t (SZ.v (S.len c.cbor_string_ptr)) }) v)

let cbor_match_tagged
  (c: cbor_tagged)
  (p: perm)
  (r: raw_data_item { Tagged? r })
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r }) -> vprop))
: Tot vprop
= exists* c' . R.pts_to c.cbor_tagged_ptr #(p `perm_mul` c.cbor_tagged_perm) c' **
    cbor_match c' (Tagged?.v r) **
    pure (c.cbor_tagged_tag == Tagged?.tag r)

let cbor_match_array
  (c: cbor_array)
  (p: perm)
  (r: raw_data_item {Array? r})
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r }) -> vprop))
: Tot vprop
= exists* v .
    A.pts_to c.cbor_array_ptr #(p `perm_mul` c.cbor_array_perm) v **
    PM.seq_list_match v (Array?.v r) cbor_match **
    pure (c.cbor_array_length == Array?.len r)

let cbor_match_map_entry
  (r0: raw_data_item)
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r0 }) -> vprop))
  (c: cbor_map_entry)
  (r: (raw_data_item & raw_data_item) { r << r0 })
: Tot vprop
= cbor_match c.cbor_map_entry_key (fst r) **
  cbor_match c.cbor_map_entry_value (snd r)

let cbor_match_map
  (c: cbor_map)
  (p: perm)
  (r: raw_data_item {Map? r})
  (cbor_match: (cbor_raw -> (v': raw_data_item { v' << r }) -> vprop))
: Tot vprop
= exists* v .
    A.pts_to c.cbor_map_ptr #(p `perm_mul` c.cbor_map_perm) v **
    PM.seq_list_match v (Map?.v r) (cbor_match_map_entry r cbor_match) **
    pure (c.cbor_map_length == Map?.len r)

let cbor_match_serialized_array
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Array? r })
: Tot vprop
= cbor_match_serialized_payload_array c p (Array?.v r) **
  pure (c.cbor_serialized_header == Array?.len r)

let cbor_match_serialized_map
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Map? r })
: Tot vprop
= cbor_match_serialized_payload_map c p (Map?.v r) **
  pure (c.cbor_serialized_header == Map?.len r)

let cbor_match_serialized_tagged
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item { Tagged? r })
: Tot vprop
= cbor_match_serialized_payload_tagged c p (Tagged?.v r) **
  pure (c.cbor_serialized_header == Tagged?.tag r)

let rec cbor_match
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
: Tot vprop
  (decreases r)
= match c, r with
  | CBOR_Case_Array v, Array _ _ -> cbor_match_array v p r (cbor_match p)
  | CBOR_Case_Map v, Map _ _ -> cbor_match_map v p r (cbor_match p)
  | CBOR_Case_Simple v, _ -> cbor_match_simple v r
  | CBOR_Case_Int v, _ -> cbor_match_int v r
  | CBOR_Case_String v, _ -> cbor_match_string v p r
  | CBOR_Case_Tagged v, Tagged _ _ -> cbor_match_tagged v p r (cbor_match p)
  | CBOR_Case_Serialized_Array v, Array _ _ -> cbor_match_serialized_array v p r
  | CBOR_Case_Serialized_Map v, Map _ _ -> cbor_match_serialized_map v p r
  | CBOR_Case_Serialized_Tagged v, Tagged _ _ -> cbor_match_serialized_tagged v p r
  | _ -> pure False
