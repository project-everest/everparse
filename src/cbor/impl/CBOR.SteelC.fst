module CBOR.SteelC

module Cbor = CBOR.SteelST.Raw
module F = Steel.ST.C.Types.Fields
module C = Steel.ST.C.Types
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module LPA = LowParse.SteelST.ArrayPtr
module LPS = LowParse.SteelST.Parse

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_string_fields =
  F.field_description_cons "byte_length" (C.scalar U64.t) (
  F.field_description_cons "payload" (C.scalar LPS.byte_array) (
  F.field_description_nil
))

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_string_byte_length : F.field_t cbor_string_fields = "byte_length"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_string_payload : F.field_t cbor_string_fields = "payload"

let cbor_string = C.struct_t "CBOR.SteelC.cbor_string" cbor_string_fields

noextract
let cbor_string_td : C.typedef cbor_string = C.struct0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_serialized_fields =
  F.field_description_cons "byte_size" (C.scalar SZ.t) (
  F.field_description_cons "payload" (C.scalar LPS.byte_array) (
  F.field_description_nil
))

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_serialized_byte_size : F.field_t cbor_serialized_fields = "byte_size"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_serialized_payload : F.field_t cbor_serialized_fields = "payload"

let cbor_serialized = C.struct_t "CBOR.SteelC.cbor_serialized" cbor_serialized_fields

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

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_tagged_tag : F.field_t cbor_tagged_fields = "tag"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_tagged_payload : F.field_t cbor_tagged_fields = "payload"

let cbor_tagged = C.struct_t "CBOR.SteelC.cbor_tagged" cbor_tagged_fields

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

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_array_count : F.field_t cbor_array_fields = "count"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_array_payload : F.field_t cbor_array_fields = "payload"

let cbor_array = C.struct_t "CBOR.SteelC.cbor_array" cbor_array_fields

noextract
let cbor_array_td : C.typedef cbor_array = C.struct0 _ _ _

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_map_fields =
  F.field_description_cons "entry_count" (C.scalar U64.t) (
  F.field_description_cons "payload" (C.scalar C.array_void_ptr) (
  F.field_description_nil
))

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_map_entry_count : F.field_t cbor_map_fields = "entry_count"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_map_payload : F.field_t cbor_map_fields = "payload"

let cbor_map = C.struct_t "CBOR.SteelC.cbor_map" cbor_map_fields

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

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_case_int64 : F.field_t cbor_case_fields = "case_int64"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_case_string : F.field_t cbor_case_fields = "case_string"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_case_tagged : F.field_t cbor_case_fields = "case_tagged"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_case_array : F.field_t cbor_case_fields = "case_array"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_case_map : F.field_t cbor_case_fields = "case_map"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_case_simple_value : F.field_t cbor_case_fields = "case_simple_value"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_case_serialized : F.field_t cbor_case_fields = "case_serialized"

let cbor_case = C.union_t "CBOR.SteelC.cbor_case" cbor_case_fields

noextract
let cbor_case_td : C.typedef cbor_case = C.union0 _ _ _

[@@CMacro]
let cbor_type_serialized = 255uy

let cbor_type_prop
  (x: U8.t)
: Tot prop
= U8.v x < pow2 3 \/
  x == cbor_type_serialized

let cbor_type_t = (x: U8.t { cbor_type_prop x })

noextract
inline_for_extraction
[@@ F.norm_field_attr]
let cbor_fields =
  F.field_description_cons "type" (C.scalar cbor_type_t) (
  F.field_description_cons "payload" cbor_case_td (
  F.field_description_nil
))

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_type : F.field_t cbor_fields = "type"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_payload : F.field_t cbor_fields = "payload"

let cbor = C.struct_t "CBOR.SteelC.cbor" cbor_fields

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

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_pair_fst : F.field_t cbor_pair_fields = "fst"

noextract inline_for_extraction [@@ F.norm_field_attr]
let cbor_pair_snd : F.field_t cbor_pair_fields = "snd"

let cbor_pair = C.struct_t "CBOR.SteelC.cbor_pair" cbor_pair_fields

noextract
let cbor_pair_td : C.typedef cbor_pair = C.struct0 _ _ _

open Steel.ST.Util

let test (#s: Ghost.erased cbor_case) (p: C.ref cbor_case_td)
: ST (Ghost.erased cbor_case)
    (C.pts_to p s)
    (fun s' -> C.pts_to p s')
    (C.full cbor_case_td s)
    (fun s' -> C.full cbor_case_td s')
= let ps = C.union_switch_field0 _ p cbor_case_int64 (C.scalar U64.t) in
  C.write ps 1729uL;
  let _ = C.ununion_field p cbor_case_int64 ps in
  drop (C.has_union_field p cbor_case_int64 _);
  let ps = C.union_field0 _ p cbor_case_int64 (C.scalar U64.t) in
  C.write ps 42uL;
  let _ = C.ununion_field p cbor_case_int64 ps in
  drop (C.has_union_field p cbor_case_int64 _);
  let s' = vpattern_replace (C.pts_to p) in
  C.full_union (Ghost.reveal s') cbor_case_int64; // FIXME: find a better pattern for that lemma
  return _

let raw_data_item_match_serialized_prop
  (c: cbor)
  (v: Cbor.raw_data_item)
  (a: LPS.byte_array)
  (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
: GTot prop
= let payload = C.struct_get_field c cbor_payload in
  C.struct_get_field c cbor_type == C.mk_scalar cbor_type_serialized /\
  C.union_get_case payload == Some cbor_case_serialized /\
  begin let payload = C.union_get_field payload cbor_case_serialized in
    C.struct_get_field payload cbor_serialized_byte_size == C.mk_scalar (LPA.len (LPS.array_of w)) /\
    w.contents == v /\
    C.struct_get_field payload cbor_serialized_payload == C.mk_scalar a
  end

[@@__reduce__]
let raw_data_item_match_serialized0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
= exists_ (fun (a: LPS.byte_array) -> exists_ (fun (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item) ->
    LPS.aparse Cbor.parse_raw_data_item a w `star`
    pure (
      raw_data_item_match_serialized_prop c v a w
    )
  ))

let raw_data_item_match_simple_value_prop
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Simple? v })
: GTot prop
= let Cbor.Simple v = v in
  let payload = C.struct_get_field c cbor_payload in
  C.struct_get_field c cbor_type == C.mk_scalar Cbor.major_type_simple_value /\
  C.union_get_case payload == Some cbor_case_simple_value /\
  C.union_get_field payload cbor_case_simple_value == C.mk_scalar v

[@@__reduce__]
let raw_data_item_match_simple_value0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Simple? v })
: Tot vprop
= pure (raw_data_item_match_simple_value_prop c v)

let raw_data_item_match_int64_prop
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Int64? v })
: GTot prop
= let Cbor.Int64 ty v = v in
  let payload = C.struct_get_field c cbor_payload in
  C.struct_get_field c cbor_type == C.mk_scalar ty /\
  C.union_get_case payload == Some cbor_case_int64 /\
  C.union_get_field payload cbor_case_int64 == C.mk_scalar v

[@@__reduce__]
let raw_data_item_match_int64_0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Int64? v })
: Tot vprop
= pure (raw_data_item_match_int64_prop c v)

module U64 = FStar.UInt64

let raw_data_item_match_string_prop
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.String? v })
  (a: LPS.byte_array)
  (w: LPA.v U8.t)
: GTot prop
= let Cbor.String ty s = v in
  let payload = C.struct_get_field c cbor_payload in
  C.struct_get_field c cbor_type == C.mk_scalar ty /\
  C.union_get_case payload == Some cbor_case_string /\
  begin let payload = C.union_get_field payload cbor_case_string in
    C.struct_get_field payload cbor_string_byte_length == C.mk_scalar (U64.uint_to_t (Seq.length s)) /\
    LPA.contents_of w == s /\
    C.struct_get_field payload cbor_string_payload == C.mk_scalar a
  end

[@@__reduce__]
let raw_data_item_match_string0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.String? v })
: Tot vprop
= exists_ (fun (a: LPS.byte_array) -> exists_ (fun (w: LPA.v U8.t) ->
    LPA.arrayptr a w `star`
    pure (
      raw_data_item_match_string_prop c v a w
    )
  ))

let raw_data_item_match_tagged_prop
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Tagged? v })
  (a: C.ref cbor_td)
: GTot prop
= let Cbor.Tagged tag v = v in
  let payload = C.struct_get_field c cbor_payload in
  C.struct_get_field c cbor_type == C.mk_scalar Cbor.major_type_tagged /\
  C.union_get_case payload == Some cbor_case_tagged /\
  begin let payload = C.union_get_field payload cbor_case_tagged in
    C.struct_get_field payload cbor_tagged_tag == C.mk_scalar tag /\
    C.struct_get_field payload cbor_tagged_payload == C.mk_scalar (C.ghost_void_ptr_of_ptr_gen a)
  end

[@@__reduce__]
let raw_data_item_match_tagged0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Tagged? v })
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: C.ref cbor_td) -> exists_ (fun (c': Ghost.erased cbor) ->
    C.pts_to a c' `star`
    raw_data_item_match c' (Cbor.Tagged?.v v) `star`
    pure (
      raw_data_item_match_tagged_prop c v a
    )
  ))

let raw_data_item_match_array_prop
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Array? v })
  (a: C.array_ptr cbor_td)
: GTot prop
= let Cbor.Array l = v in
  let payload = C.struct_get_field c cbor_payload in
  C.struct_get_field c cbor_type == C.mk_scalar Cbor.major_type_array /\
  C.union_get_case payload == Some cbor_case_array /\
  begin let payload = C.union_get_field payload cbor_case_array in
    C.struct_get_field payload cbor_array_count == C.mk_scalar (U64.uint_to_t (List.Tot.length l)) /\
    C.struct_get_field payload cbor_array_payload == C.mk_scalar a
  end

[@@__reduce__]
let raw_data_item_match_array0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Array? v })
  (raw_data_item_array_match: (Seq.seq cbor -> (v': list Cbor.raw_data_item { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: C.array cbor_td) -> exists_ (fun (c': Ghost.erased (Seq.seq cbor)) ->
    C.array_pts_to a c' `star`
    raw_data_item_array_match c' (Cbor.Array?.v v) `star`
    pure (
      raw_data_item_match_array_prop c v (C.array_ptr_of a)
    )
  ))

let raw_data_item_match_map_prop
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Map? v })
  (a: C.array_ptr cbor_pair_td)
: GTot prop
= let Cbor.Map l = v in
  let payload = C.struct_get_field c cbor_payload in
  C.struct_get_field c cbor_type == C.mk_scalar Cbor.major_type_map /\
  C.union_get_case payload == Some cbor_case_map /\
  begin let payload = C.union_get_field payload cbor_case_map in
    C.struct_get_field payload cbor_map_entry_count == C.mk_scalar (U64.uint_to_t (List.Tot.length l)) /\
    C.struct_get_field payload cbor_map_payload == C.mk_scalar a
  end

[@@__reduce__]
let raw_data_item_match_map0
  (c: cbor)
  (v: Cbor.raw_data_item { Cbor.Map? v })
  (raw_data_item_map_match: (Seq.seq cbor_pair -> (v': list (Cbor.raw_data_item & Cbor.raw_data_item) { v' << v }) -> vprop))
: Tot vprop
= exists_ (fun (a: C.array cbor_pair_td) -> exists_ (fun (c': Ghost.erased (Seq.seq cbor_pair)) ->
    C.array_pts_to a c' `star`
    raw_data_item_map_match c' (Cbor.Map?.v v) `star`
    pure (
      raw_data_item_match_map_prop c v (C.array_ptr_of a)
    )
  ))

[@@__reduce__]
let raw_data_item_array_match_nil0
  (c: Seq.seq cbor)
: Tot vprop
= pure (c `Seq.equal` Seq.empty)

[@@__reduce__]
let raw_data_item_array_match_cons0
  (c: Seq.seq cbor)
  (l: list Cbor.raw_data_item { Cons? l })
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << l }) -> vprop))
  (raw_data_item_array_match: (Seq.seq cbor -> (v': list Cbor.raw_data_item { v' << l }) -> vprop))
: Tot vprop
= exists_ (fun (c1: cbor) -> exists_ (fun (c2: Seq.seq cbor) ->
    raw_data_item_match c1 (List.Tot.hd l) `star`
    raw_data_item_array_match c2 (List.Tot.tl l) `star`
    pure (c `Seq.equal` Seq.cons c1 c2)
  ))

[@@__reduce__]
let raw_data_item_map_match_nil0
  (c: Seq.seq cbor_pair)
: Tot vprop
= pure (c `Seq.equal` Seq.empty)

noextract
let fstp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a1 = fst x

noextract
let sndp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a2 = snd x

[@@__reduce__]
let raw_data_item_map_match_cons0
  (c: Seq.seq cbor_pair)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item) { Cons? l })
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << l }) -> vprop))
  (raw_data_item_map_match: (Seq.seq cbor_pair -> (v': list (Cbor.raw_data_item & Cbor.raw_data_item) { v' << l }) -> vprop))
: Tot vprop
= exists_ (fun (c1: cbor_pair) -> exists_ (fun (c2: Seq.seq cbor_pair) ->
    raw_data_item_match (C.struct_get_field c1 cbor_pair_fst) (fstp (List.Tot.hd l)) `star`
    raw_data_item_match (C.struct_get_field c1 cbor_pair_snd) (sndp (List.Tot.hd l)) `star`
    raw_data_item_map_match c2 (List.Tot.tl l) `star`
    pure (c `Seq.equal` Seq.cons c1 c2)
  ))

let rec raw_data_item_match0
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= if C.get_scalar_value (C.struct_get_field c cbor_type) = Some cbor_type_serialized
  then raw_data_item_match_serialized0 c v
  else match v with
  | Cbor.Simple _ -> raw_data_item_match_simple_value0 c v
  | Cbor.Int64 _ _ -> raw_data_item_match_int64_0 c v
  | Cbor.String _ _ -> raw_data_item_match_string0 c v
  | Cbor.Array _ -> raw_data_item_match_array0 c v raw_data_item_array_match0
  | Cbor.Map _ -> raw_data_item_match_map0 c v raw_data_item_map_match0
  | Cbor.Tagged _ _ -> raw_data_item_match_tagged0 c v raw_data_item_match0

and raw_data_item_array_match0
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= match v with
  | [] -> raw_data_item_array_match_nil0 c
  | _ :: _ -> raw_data_item_array_match_cons0 c v raw_data_item_match0 raw_data_item_array_match0

and raw_data_item_map_match0
  (c: Seq.seq cbor_pair)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= match v with
  | [] -> raw_data_item_map_match_nil0 c
  | _ :: _ -> raw_data_item_map_match_cons0 c v raw_data_item_match0 raw_data_item_map_match0

irreducible
let raw_data_item_match : (phi: (
  (c: cbor) ->
  (v: Cbor.raw_data_item) ->
  Tot vprop
) {phi == raw_data_item_match0}
) = raw_data_item_match0

let raw_data_item_match_eq : squash (raw_data_item_match == raw_data_item_match0) = ()

let raw_data_item_match_intro_serialized
  (#opened: _)
  (c: Ghost.erased cbor)
  (v: Cbor.raw_data_item)
  (a: LPS.byte_array)
  (w: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
: STGhost unit opened
    (LPS.aparse Cbor.parse_raw_data_item a w)
    (fun _ -> raw_data_item_match (Ghost.reveal c) v)
    (raw_data_item_match_serialized_prop (Ghost.reveal c) v a w)
    (fun _ -> True)
= noop ();
  rewrite
    (raw_data_item_match_serialized0 c v)
    (raw_data_item_match c v)

#restart-solver

let read_valid_cbor_from_buffer
  (#va: LPS.v Cbor.parse_raw_data_item_kind Cbor.raw_data_item)
  (#c: Ghost.erased cbor)
  (a: LPS.byte_array)
  (alen: SZ.t)
  (tgt: C.ref cbor_td)
: ST (Ghost.erased cbor)
    (LPS.aparse Cbor.parse_raw_data_item a va `star`
      C.pts_to tgt c
    )
    (fun c' ->
      C.pts_to tgt c'
      `star` raw_data_item_match (Ghost.reveal c') va.contents
    )
    (alen == LPA.len (LPS.array_of va) /\
      C.full cbor_td c
    )
    (fun c' -> C.full cbor_td c')
=
  let ptype = C.struct_field1 _ tgt cbor_type (C.scalar cbor_type_t) (_ by (F.norm_fields ())) (_ by (F.norm_fields ())) in
  C.write ptype cbor_type_serialized;
  let _ = C.unstruct_field_and_drop tgt cbor_type ptype in
  let payload1 = C.struct_field1 _ tgt cbor_payload cbor_case_td (_ by (F.norm_fields ())) (_ by (F.norm_fields ())) in
  let payload2 = C.union_switch_field1 _ payload1 cbor_case_serialized cbor_serialized_td (_ by (F.norm_fields ())) (_ by (F.norm_fields ())) in
  let plen = C.struct_field1 _ payload2 cbor_serialized_byte_size (C.scalar SZ.t) (_ by (F.norm_fields ())) (_ by (F.norm_fields ())) in
  C.write plen alen;
  let _ = C.unstruct_field_and_drop payload2 cbor_serialized_byte_size plen in
  let payload3 = C.struct_field1 _ payload2 cbor_serialized_payload (C.scalar LPS.byte_array) (_ by (F.norm_fields ())) (_ by (F.norm_fields ())) in
  C.write payload3 a;
  let _ = C.unstruct_field_and_drop payload2 cbor_serialized_payload payload3 in
  let _ = C.ununion_field_and_drop payload1 cbor_case_serialized payload2 in
  let _ = C.unstruct_field_and_drop tgt cbor_payload payload1 in
  let c' = vpattern_replace (C.pts_to tgt) in
  raw_data_item_match_intro_serialized c' va.contents a va;
  return c'

let cbor_int64_type_some
  (#opened: _)
  (c: cbor)
  (va: Cbor.raw_data_item)
: STGhost unit opened
    (raw_data_item_match c va)
    (fun _ -> raw_data_item_match c va)
    (Cbor.Int64? va)
    (fun _ -> Some? (C.get_scalar_value (C.struct_get_field c cbor_type)))
= if C.get_scalar_value (C.struct_get_field c cbor_type) = Some cbor_type_serialized
  then
    noop ()
  else begin
    rewrite
      (raw_data_item_match c va)
      (raw_data_item_match_int64_0 c va);
    let _ = Steel.ST.GenElim.gen_elim () in
    rewrite
      (raw_data_item_match_int64_0 c va)
      (raw_data_item_match c va)
  end

#push-options "--z3rlimit 16"
#restart-solver

let read_cbor_int64
  (#va: Ghost.erased Cbor.raw_data_item)
  (#c: Ghost.erased cbor)
  (x: C.ref cbor_td)
: ST (Ghost.erased cbor)
    (C.pts_to x c
      `star` raw_data_item_match (Ghost.reveal c) va
    )
    (fun c' ->
      C.pts_to x c'
      `star` raw_data_item_match (Ghost.reveal c') va
    )
    (Cbor.Int64? va /\
      C.full cbor_td (Ghost.reveal c)
    )
    (fun c' ->
      C.full cbor_td (Ghost.reveal c')
    )
= cbor_int64_type_some c va;
  let ptyp = C.struct_field x cbor_type () in
  let typ : cbor_type_t = C.read ptyp in
  if (typ <: U8.t) = cbor_type_serialized
  then begin
    rewrite
      (raw_data_item_match c va)
      (raw_data_item_match_serialized0 c va);
    let _ = Steel.ST.GenElim.gen_elim () in
    let payload1 = C.struct_field x cbor_payload () in
    let v1 = vpattern_replace (C.pts_to payload1) in
    let _ : squash (C.union_get_case (Ghost.reveal v1) == Some cbor_case_serialized) = () in
    let payload2 = C.union_field payload1 cbor_case_serialized () in
    let pa = C.struct_field payload2 cbor_serialized_payload () in
    let a = C.read pa in
    let _ = C.unstruct_field_and_drop payload2 cbor_serialized_payload pa in
    vpattern_rewrite (fun a -> LPS.aparse _ a _) a;
    let ty = Cbor.read_major_type a in
    let v = Cbor.read_int64 a in
    let _ = C.ununion_field_and_drop payload1 cbor_case_serialized payload2 in
    let payload2' = C.union_switch_field payload1 cbor_case_int64 () in
    C.write payload2' v;
    let _ = C.ununion_field_and_drop payload1 cbor_case_int64 payload2' in
    let _ = C.unstruct_field_and_drop x cbor_payload payload1 in
    C.write ptyp ty;
    let c' = C.unstruct_field_and_drop x cbor_type ptyp in
    drop (LPS.aparse _ _ _);
    rewrite
      (raw_data_item_match_int64_0 c' va)
      (raw_data_item_match c' va);
    return c'
  end else begin
    let c' = C.unstruct_field_and_drop x cbor_type ptyp in
    assert (C.struct_eq c c');
    vpattern_rewrite (C.pts_to x) c;
    noop ();
    return c
  end

#pop-options
