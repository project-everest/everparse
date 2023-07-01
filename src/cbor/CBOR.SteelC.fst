module CBOR.SteelC

module Cs = Steel.ST.C.Types.UserStruct
module C = Steel.ST.C.Types
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT

inline_for_extraction
noextract
type union_item ([@@@strictly_positive] t: Type) (p: option bool) (one: t) = (x: t {
  match p with
  | None -> True
  | Some p -> not p == FStar.StrongExcludedMiddle.strong_excluded_middle (x == one)
})

[@@erasable]
noeq
type cbor_case_tag =
| CBORCaseInt64
| CBORCaseString
| CBORCaseTagged
| CBORCaseArray
| CBORCaseMap
| CBORCaseSimpleValue
| CBORCaseSerialized

noeq
type cbor_string = {
  cbor_string_byte_length: C.scalar_t U64.t;
  cbor_string_payload: C.scalar_t (C.array (C.scalar U8.t));
}

noeq
type cbor_serialized = {
  cbor_serialized_byte_size: C.scalar_t SZ.t;
  cbor_serialized_payload: C.scalar_t (C.array (C.scalar U8.t));
}

let cbor_serialized_one : Ghost.erased cbor_serialized = Ghost.hide {
  cbor_serialized_byte_size = C.unknown (C.scalar SZ.t);
  cbor_serialized_payload = C.unknown (C.scalar (C.array (C.scalar U8.t)));
}

noeq
type cbor_tagged (active: Ghost.erased (option bool)) = {
  cbor_tagged_tag: union_item (C.scalar_t U64.t) active (C.unknown (C.scalar U64.t));
  cbor_tagged_payload: union_item (C.scalar_t (C.ptr_gen cbor)) active (C.unknown (C.scalar (C.ptr_gen cbor)));
}
and cbor_array (active: Ghost.erased (option bool)) = {
  cbor_array_count: union_item (C.scalar_t U64.t) active (C.unknown (C.scalar U64.t));
  cbor_array_payload: union_item (C.scalar_t (C.array_ptr_gen cbor)) active (C.unknown (C.scalar (C.array_ptr_gen cbor)));
}
and cbor_map (active: Ghost.erased (option bool)) = {
  cbor_map_entry_count: C.scalar_t U64.t;
  cbor_map_payload: C.scalar_t (C.ptr_gen cbor_pair);
}
and cbor_case = { // TODO: find a way to extract this struct as an union
  cbor_case_tag: cbor_case_tag;
  cbor_case_int64: union_item (C.scalar_t U64.t) (Some (CBORCaseInt64? cbor_case_tag)) (C.unknown (C.scalar U64.t));
  cbor_case_tagged: cbor_tagged (Some (CBORCaseTagged? cbor_case_tag));
  cbor_case_array: cbor_array (Some (CBORCaseArray? cbor_case_tag));
  cbor_case_map: cbor_map (Some (CBORCaseMap? cbor_case_tag));
  cbor_case_simple_value: union_item (C.scalar_t U8.t) (Some (CBORCaseSimpleValue? cbor_case_tag)) (C.unknown (C.scalar U8.t));
  cbor_case_serialized: union_item cbor_serialized (Some (CBORCaseSerialized? cbor_case_tag)) cbor_serialized_one;
}
and cbor = {
  cbor_type: U8.t;
  cbor_payload: cbor_case;
}
and cbor_pair = {
  cbor_pair_fst: cbor;
  cbor_pair_snd: cbor;
}
