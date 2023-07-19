module CBOR.SteelC

module Cbor = CBOR.Spec
module F = Steel.ST.C.Types.Fields
module C = Steel.ST.C.Types
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_string_fields =
  F.field_description_cons "byte_length" (C.scalar U64.t) (
  F.field_description_cons "payload" (C.scalar (C.array (C.scalar U8.t)))
  F.field_description_nil)

let cbor_string = C.struct_t "" cbor_string_fields

noextract
let cbor_string_td : C.typedef cbor_string = C.struct0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_serialized_fields =
  F.field_description_cons "byte_size" (C.scalar SZ.t) (
  F.field_description_cons "payload" (C.scalar (C.array (C.scalar U8.t)))
  F.field_description_nil)

let cbor_serialized = C.struct_t "" cbor_serialized_fields

noextract
let cbor_serialized_td : C.typedef cbor_serialized = C.struct0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_tagged_fields =
  F.field_description_cons "tag" (C.scalar U64.t) (
  F.field_description_cons "payload" (C.scalar C.void_ptr) (
  F.field_description_nil
))

let cbor_tagged = C.struct_t "" cbor_tagged_fields

noextract
let cbor_tagged_td : C.typedef cbor_tagged = C.struct0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_array_fields =
  F.field_description_cons "count" (C.scalar U64.t) (
  F.field_description_cons "payload" (C.scalar C.array_void_ptr) (
  F.field_description_nil
))

let cbor_array = C.struct_t "" cbor_array_fields

noextract
let cbor_array_td : C.typedef cbor_array = C.struct0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_map_fields =
  F.field_description_cons "entry_count" (C.scalar U64.t) (
  F.field_description_cons "payload" (C.scalar C.void_ptr) (
  F.field_description_nil
))

let cbor_map = C.struct_t "" cbor_map_fields

noextract
let cbor_map_td : C.typedef cbor_map = C.struct0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_case_fields =
  F.field_description_cons "case_int64" (C.scalar U64.t) (
  F.field_description_cons "case_string" cbor_string_td (
  F.field_description_cons "case_tagged" cbor_tagged_td (
  F.field_description_cons "case_array" cbor_array_td (
  F.field_description_cons "case_map" cbor_map_td (
  F.field_description_cons "case_simple_value" (C.scalar Cbor.simple_value) (
  F.field_description_cons "case_serialized" cbor_serialized_td (
  F.field_description_nil
)))))))

let cbor_case = C.union_t "" cbor_case_fields

noextract
let cbor_case_td : C.typedef cbor_case = C.union0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_fields =
  F.field_description_cons "type" (C.scalar Cbor.major_type_t) (
  F.field_description_cons "payload" cbor_case_td (
  F.field_description_nil
))

let cbor = C.struct_t "" cbor_fields

noextract
let cbor_td : C.typedef cbor = C.struct0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_pair_fields =
  F.field_description_cons "fst" cbor_td (
  F.field_description_cons "snd" cbor_td (
  F.field_description_nil
))

let cbor_pair = C.struct_t "" cbor_pair_fields

noextract
let cbor_pair_td : C.typedef cbor_pair = C.struct0 _ _ _

open Steel.ST.Util

#set-options "--print_implicits"

let test (#s: Ghost.erased cbor_case) (p: C.ref cbor_case_td)
: ST (Ghost.erased cbor_case)
    (C.pts_to p s)
    (fun s' -> C.pts_to p s')
    (C.full cbor_case_td s)
    (fun s' -> C.full cbor_case_td s')
= let ps = C.union_switch_field0 _ p "case_int64" (C.scalar U64.t) in
  C.write ps 1729uL;
  let _ = C.ununion_field p "case_int64" ps in
  drop (C.has_union_field p "case_int64" _);
  let ps = C.union_field0 _ p "case_int64" (C.scalar U64.t) in
  C.write ps 42uL;
  let _ = C.ununion_field p "case_int64" ps in
  drop (C.has_union_field p "case_int64" _);
  let s' = vpattern_replace (C.pts_to p) in
  C.full_union (Ghost.reveal s') "case_int64"; // FIXME: find a better pattern for that lemma
  return _
