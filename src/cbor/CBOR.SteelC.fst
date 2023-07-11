module CBOR.SteelC

module Cbor = CBOR.Spec
module Cs = Steel.ST.C.Types.UserStruct
module Cu = Steel.ST.C.Types.UserUnion
module F = Steel.ST.C.Types.Fields
module C = Steel.ST.C.Types
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module RW = Steel.ST.C.Rewrite

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
let cbor_case_known_tag : Cs.nonempty_set string =
  FStar.Set.empty
  `Cs.set_snoc` "cbor_case_int64"
  `Cs.set_snoc` "cbor_case_string"
  `Cs.set_snoc` "cbor_case_tagged"
  `Cs.set_snoc` "cbor_case_array"
  `Cs.set_snoc` "cbor_case_map"
  `Cs.set_snoc` "cbor_case_simple_value"
  `Cs.set_snoc` "cbor_case_serialized"

noeq
type cbor_tagged (active: Ghost.erased (option bool)) = {
  cbor_tagged_tag: C.scalar_t U64.t;
  cbor_tagged_payload: C.scalar_t (C.ptr_gen cbor);
  cbor_tagged_active: squash (match Ghost.reveal active with
  | None -> True
  | Some tag_active -> (tag_active == false <==> (cbor_tagged_tag == C.unknown (C.scalar U64.t) /\ cbor_tagged_payload == C.unknown (C.scalar (C.ptr_gen cbor))))
  );
}
and cbor_array (active: Ghost.erased (option bool)) = {
  cbor_array_count: C.scalar_t U64.t;
  cbor_array_payload: C.scalar_t (C.array_ptr_gen cbor);
  cbor_array_active: squash (match Ghost.reveal active with
  | None -> True
  | Some tag_active -> (tag_active == false <==> (cbor_array_count == C.unknown (C.scalar U64.t) /\ cbor_array_payload == C.unknown (C.scalar (C.array_ptr_gen cbor))))
  );
}
and cbor_map (active: Ghost.erased (option bool)) = {
  cbor_map_entry_count: C.scalar_t U64.t;
  cbor_map_payload: C.scalar_t (C.ptr_gen cbor_pair);
  cbor_map_active: squash (match Ghost.reveal active with
  | None -> True
  | Some tag_active -> (tag_active == false <==> (cbor_map_entry_count == C.unknown (C.scalar U64.t) /\ cbor_map_payload == C.unknown (C.scalar (C.ptr_gen cbor_pair))))
  );
}
and cbor_case = { // TODO: find a way to extract this struct as an union
  cbor_case_tag: Ghost.erased (Cu.union_tag (Cs.set_def cbor_case_known_tag));
  cbor_case_int64: Cu.union_item_t (C.scalar_t U64.t) (C.unknown (C.scalar U64.t)) (Some (Cu.TagKnown (Some "cbor_case_int64") = Ghost.reveal cbor_case_tag));
  cbor_case_string: Cu.union_item_t cbor_string (C.unknown cbor_string_td) (Some (Cu.TagKnown (Some "cbor_case_string") = Ghost.reveal cbor_case_tag));
  cbor_case_tagged: cbor_tagged (Some (Cu.TagKnown (Some "cbor_case_tagged") = Ghost.reveal cbor_case_tag));
  cbor_case_array: cbor_array (Some (Cu.TagKnown (Some "cbor_case_array") = Ghost.reveal cbor_case_tag));
  cbor_case_map: cbor_map (Some (Cu.TagKnown (Some "cbor_case_map") = Ghost.reveal cbor_case_tag));
  cbor_case_simple_value: Cu.union_item_t (C.scalar_t Cbor.simple_value) (C.unknown (C.scalar Cbor.simple_value)) (Some (Cu.TagKnown (Some "cbor_case_simple_value") = Ghost.reveal cbor_case_tag));
  cbor_case_serialized: Cu.union_item_t cbor_serialized (C.unknown cbor_serialized_td) (Some (Cu.TagKnown (Some "cbor_case_serialized") = Ghost.reveal cbor_case_tag));
  cbor_case_unknown: Cu.union_item_t (C.scalar_t (squash False)) (C.unknown (C.scalar (squash False))) (Some (Cu.TagKnown None = Ghost.reveal cbor_case_tag));
}
and cbor = {
  cbor_type: C.scalar_t Cbor.major_type_t;
  cbor_payload: cbor_case;
}
and cbor_pair = {
  cbor_pair_fst: cbor;
  cbor_pair_snd: cbor;
}

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_tagged_struct_def : Cs.struct_def (cbor_tagged None) =
  let fields = FStar.Set.empty `Cs.set_snoc` "cbor_tagged_tag" `Cs.set_snoc` "cbor_tagged_payload" in
  let field_desc : Steel.ST.C.Types.Struct.Aux.field_description_gen_t (Cs.field_t fields) = {
    fd_nonempty = Cs.nonempty_set_nonempty_type "cbor_tagged_tag" fields;
    fd_type = (fun (n: Cs.field_t fields) -> match n with "cbor_tagged_tag" -> C.scalar_t U64.t | "cbor_tagged_payload" -> C.scalar_t (C.ptr_gen cbor));
    fd_typedef = (fun (n: Cs.field_t fields) -> match n with "cbor_tagged_tag" -> C.scalar U64.t | "cbor_tagged_payload" -> C.scalar (C.ptr_gen cbor));
  }
  in {
  fields = fields;
  field_desc = field_desc;
  mk = (fun f -> Mkcbor_tagged (f "cbor_tagged_tag") (f "cbor_tagged_payload") ());
  get = (fun (x: cbor_tagged None) (f: Cs.field_t fields) -> match f with "cbor_tagged_tag" -> x.cbor_tagged_tag | "cbor_tagged_payload" -> x.cbor_tagged_payload);
  get_mk = (fun _ _ -> ());
  extensionality = (fun s1 s2 phi -> phi "cbor_tagged_tag"; phi "cbor_tagged_payload")
}

noextract
let cbor_tagged_td : C.typedef (cbor_tagged None) = Cs.struct_typedef cbor_tagged_struct_def

let cbor_tagged_unknown : Ghost.erased (cbor_tagged None) = Ghost.hide ({
  cbor_tagged_tag = C.unknown (C.scalar U64.t);
  cbor_tagged_payload = C.unknown (C.scalar (C.ptr_gen cbor));
  cbor_tagged_active = ();
})

let cbor_tagged_unknown_eq : squash (C.unknown cbor_tagged_td == Ghost.reveal cbor_tagged_unknown) =
  cbor_tagged_struct_def.extensionality (C.unknown (cbor_tagged_td)) (Ghost.reveal cbor_tagged_unknown) (fun _ -> ())

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_tagged_is_union_item : Cu.is_union_item cbor_tagged (C.unknown cbor_tagged_td) = {
  some_to_none = (fun _ x -> Mkcbor_tagged x.cbor_tagged_tag x.cbor_tagged_payload ());
  none_to_some = (fun x -> Mkcbor_tagged x.cbor_tagged_tag x.cbor_tagged_payload ());
  none_to_some_inj = (fun x -> ());
  some_to_none_inj = (fun _ x -> ());
}

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_array_struct_def : Cs.struct_def (cbor_array None) =
  let fields = FStar.Set.empty `Cs.set_snoc` "cbor_array_count" `Cs.set_snoc` "cbor_array_payload" in
  let field_desc : Steel.ST.C.Types.Struct.Aux.field_description_gen_t (Cs.field_t fields) = {
    fd_nonempty = Cs.nonempty_set_nonempty_type "cbor_array_count" fields;
    fd_type = (fun (n: Cs.field_t fields) -> match n with "cbor_array_count" -> C.scalar_t U64.t | "cbor_array_payload" -> C.scalar_t (C.array_ptr_gen cbor));
    fd_typedef = (fun (n: Cs.field_t fields) -> match n with "cbor_array_count" -> C.scalar U64.t | "cbor_array_payload" -> C.scalar (C.array_ptr_gen cbor));
  }
  in {
  fields = fields;
  field_desc = field_desc;
  mk = (fun f -> Mkcbor_array (f "cbor_array_count") (f "cbor_array_payload") ());
  get = (fun (x: cbor_array None) (f: Cs.field_t fields) -> match f with "cbor_array_count" -> x.cbor_array_count | "cbor_array_payload" -> x.cbor_array_payload);
  get_mk = (fun _ _ -> ());
  extensionality = (fun s1 s2 phi -> phi "cbor_array_count"; phi "cbor_array_payload")
}

noextract
let cbor_array_td : C.typedef (cbor_array None) = Cs.struct_typedef cbor_array_struct_def

let cbor_array_unknown : Ghost.erased (cbor_array None) = Ghost.hide ({
  cbor_array_count = C.unknown (C.scalar U64.t);
  cbor_array_payload = C.unknown (C.scalar (C.array_ptr_gen cbor));
  cbor_array_active = ();
})

let cbor_array_unknown_eq : squash (C.unknown cbor_array_td == Ghost.reveal cbor_array_unknown) =
  cbor_array_struct_def.extensionality (C.unknown (cbor_array_td)) (Ghost.reveal cbor_array_unknown) (fun _ -> ())

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_array_is_union_item : Cu.is_union_item cbor_array (C.unknown cbor_array_td) = {
  some_to_none = (fun _ x -> Mkcbor_array x.cbor_array_count x.cbor_array_payload ());
  none_to_some = (fun x -> Mkcbor_array x.cbor_array_count x.cbor_array_payload ());
  none_to_some_inj = (fun x -> ());
  some_to_none_inj = (fun _ x -> ());
}

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_map_struct_def : Cs.struct_def (cbor_map None) =
  let fields = FStar.Set.empty `Cs.set_snoc` "cbor_map_entry_count" `Cs.set_snoc` "cbor_map_payload" in
  let field_desc : Steel.ST.C.Types.Struct.Aux.field_description_gen_t (Cs.field_t fields) = {
    fd_nonempty = Cs.nonempty_set_nonempty_type "cbor_map_entry_count" fields;
    fd_type = (fun (n: Cs.field_t fields) -> match n with "cbor_map_entry_count" -> C.scalar_t U64.t | "cbor_map_payload" -> C.scalar_t (C.ptr_gen cbor_pair));
    fd_typedef = (fun (n: Cs.field_t fields) -> match n with "cbor_map_entry_count" -> C.scalar U64.t | "cbor_map_payload" -> C.scalar (C.ptr_gen cbor_pair));
  }
  in {
  fields = fields;
  field_desc = field_desc;
  mk = (fun f -> Mkcbor_map (f "cbor_map_entry_count") (f "cbor_map_payload") ());
  get = (fun (x: cbor_map None) (f: Cs.field_t fields) -> match f with "cbor_map_entry_count" -> x.cbor_map_entry_count | "cbor_map_payload" -> x.cbor_map_payload);
  get_mk = (fun _ _ -> ());
  extensionality = (fun s1 s2 phi -> phi "cbor_map_entry_count"; phi "cbor_map_payload")
}

noextract
let cbor_map_td : C.typedef (cbor_map None) = Cs.struct_typedef cbor_map_struct_def

let cbor_map_unknown : Ghost.erased (cbor_map None) = Ghost.hide ({
  cbor_map_entry_count = C.unknown (C.scalar U64.t);
  cbor_map_payload = C.unknown (C.scalar (C.ptr_gen cbor_pair));
  cbor_map_active = ();
})

let cbor_map_unknown_eq : squash (C.unknown cbor_map_td == Ghost.reveal cbor_map_unknown) =
  cbor_map_struct_def.extensionality (C.unknown (cbor_map_td)) (Ghost.reveal cbor_map_unknown) (fun _ -> ())

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_map_is_union_item : Cu.is_union_item cbor_map (C.unknown cbor_map_td) = {
  some_to_none = (fun _ x -> Mkcbor_map x.cbor_map_entry_count x.cbor_map_payload ());
  none_to_some = (fun x -> Mkcbor_map x.cbor_map_entry_count x.cbor_map_payload ());
  none_to_some_inj = (fun x -> ());
  some_to_none_inj = (fun _ x -> ());
}

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_case_field_desc : F.field_description_t unit = {
  fd_def = Cs.set_def cbor_case_known_tag;
  fd_empty = false;
  fd_type = (fun f -> match f with 
  | "cbor_case_int64" -> C.scalar_t U64.t
  | "cbor_case_string" -> cbor_string
  | "cbor_case_tagged" -> cbor_tagged None
  | "cbor_case_array" -> cbor_array None
  | "cbor_case_map" -> cbor_map None
  | "cbor_case_simple_value" -> C.scalar_t Cbor.simple_value 
  | "cbor_case_serialized" -> cbor_serialized
  | _ -> squash False
  );
  fd_typedef = (fun f -> match f with 
  | "cbor_case_int64" -> C.scalar U64.t
  | "cbor_case_string" -> cbor_string_td
  | "cbor_case_tagged" -> cbor_tagged_td
  | "cbor_case_array" -> cbor_array_td
  | "cbor_case_map" -> cbor_map_td
  | "cbor_case_simple_value" -> C.scalar Cbor.simple_value 
  | "cbor_case_serialized" -> cbor_serialized_td
  );
}

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_case_union_field_desc : Cu.union_field_description_t cbor_case_field_desc = {
  fd_union_type = (fun f -> match f with
  | "cbor_case_int64" -> Cu.union_item_t (C.scalar_t U64.t) (C.unknown (C.scalar U64.t))
  | "cbor_case_string" -> Cu.union_item_t cbor_string (C.unknown cbor_string_td)
  | "cbor_case_tagged" -> cbor_tagged
  | "cbor_case_array" -> cbor_array
  | "cbor_case_map" -> cbor_map
  | "cbor_case_simple_value" -> Cu.union_item_t (C.scalar_t Cbor.simple_value) (C.unknown (C.scalar Cbor.simple_value))
  | "cbor_case_serialized" -> Cu.union_item_t cbor_serialized (C.unknown cbor_serialized_td)
  );
  fd_union_type_rewrite = (fun f -> match f with
  | "cbor_case_int64" -> Cu.union_item_rewrite (C.unknown (C.scalar U64.t))
  | "cbor_case_string" -> Cu.union_item_rewrite (C.unknown cbor_string_td)
  | "cbor_case_tagged" -> RW.rewrite_id (cbor_tagged None)
  | "cbor_case_array" -> RW.rewrite_id (cbor_array None)
  | "cbor_case_map" -> RW.rewrite_id (cbor_map None)
  | "cbor_case_simple_value" -> Cu.union_item_rewrite (C.unknown (C.scalar Cbor.simple_value))
  | "cbor_case_serialized" -> Cu.union_item_rewrite (C.unknown cbor_serialized_td)
  );
  fd_union_item = (fun f -> match f with
  | "cbor_case_int64" -> Cu.union_item_gen (C.scalar U64.t)
  | "cbor_case_string" -> Cu.union_item_gen cbor_string_td
  | "cbor_case_tagged" -> cbor_tagged_is_union_item
  | "cbor_case_array" -> cbor_array_is_union_item
  | "cbor_case_map" -> cbor_map_is_union_item
  | "cbor_case_simple_value" -> Cu.union_item_gen (C.scalar Cbor.simple_value)
  | "cbor_case_serialized" -> Cu.union_item_gen cbor_serialized_td
  );
}

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_case_union_def : Cu.union_def cbor_case unit = {
  fields = cbor_case_field_desc;
  field_desc = cbor_case_union_field_desc;
  mk = (fun tag phi -> {
    cbor_case_tag = tag;
    cbor_case_int64 = phi (Some "cbor_case_int64");
    cbor_case_string = phi (Some "cbor_case_string");
    cbor_case_tagged = phi (Some "cbor_case_tagged");
    cbor_case_array = phi (Some "cbor_case_array");
    cbor_case_map = phi (Some "cbor_case_map");
    cbor_case_simple_value = phi (Some "cbor_case_simple_value");
    cbor_case_serialized = phi (Some "cbor_case_serialized");
    cbor_case_unknown = phi None;
  });
  get_tag = (fun x -> x.cbor_case_tag);
  get = (fun x tag' -> match tag' with
  | Some "cbor_case_int64" -> x.cbor_case_int64
  | Some "cbor_case_string" -> x.cbor_case_string
  | Some "cbor_case_tagged" -> x.cbor_case_tagged
  | Some "cbor_case_array" -> x.cbor_case_array
  | Some "cbor_case_map" -> x.cbor_case_map
  | Some "cbor_case_simple_value" -> x.cbor_case_simple_value
  | Some "cbor_case_serialized" -> x.cbor_case_serialized
  | None -> x.cbor_case_unknown
  );
  get_tag_mk = (fun tag phi -> ());
  get_mk = (fun tag phi f -> ());
  extensionality = (fun x1 x2 prf_tag phi ->
    phi (Some "cbor_case_int64");
    phi (Some "cbor_case_string");
    phi (Some "cbor_case_tagged");
    phi (Some "cbor_case_array");
    phi (Some "cbor_case_map");
    phi (Some "cbor_case_simple_value");
    phi (Some "cbor_case_serialized");
    phi None
  );
}

noextract
let cbor_case_td : C.typedef cbor_case = Cu.union_typedef cbor_case_union_def

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_struct_def : Cs.struct_def cbor =
  let fields = FStar.Set.empty `Cs.set_snoc` "cbor_type" `Cs.set_snoc` "cbor_payload" in
  let field_desc : Steel.ST.C.Types.Struct.Aux.field_description_gen_t (Cs.field_t fields) = {
    fd_nonempty = Cs.nonempty_set_nonempty_type "cbor_type" fields;
    fd_type = (fun (n: Cs.field_t fields) -> match n with "cbor_type" -> C.scalar_t Cbor.major_type_t | "cbor_payload" -> cbor_case);
    fd_typedef = (fun (n: Cs.field_t fields) -> match n with "cbor_type" -> C.scalar Cbor.major_type_t | "cbor_payload" -> cbor_case_td);
  }
  in {
  fields = fields;
  field_desc = field_desc;
  mk = (fun f -> Mkcbor (f "cbor_type") (f "cbor_payload"));
  get = (fun (x: cbor) (f: Cs.field_t fields) -> match f with "cbor_type" -> x.cbor_type | "cbor_payload" -> x.cbor_payload);
  get_mk = (fun _ _ -> ());
  extensionality = (fun s1 s2 phi -> phi "cbor_type"; phi "cbor_payload")
}

noextract
let cbor_td : C.typedef cbor = Cs.struct_typedef cbor_struct_def

noextract
inline_for_extraction
[@@F.norm_field_attr]
let cbor_pair_struct_def : Cs.struct_def cbor_pair =
  let fields = FStar.Set.empty `Cs.set_snoc` "cbor_pair_fst" `Cs.set_snoc` "cbor_pair_snd" in
  let field_desc : Steel.ST.C.Types.Struct.Aux.field_description_gen_t (Cs.field_t fields) = {
    fd_nonempty = Cs.nonempty_set_nonempty_type "cbor_pair_fst" fields;
    fd_type = (fun _ -> cbor);
    fd_typedef = (fun _ -> cbor_td);
  }
  in {
  fields = fields;
  field_desc = field_desc;
  mk = (fun f -> Mkcbor_pair (f "cbor_pair_fst") (f "cbor_pair_snd"));
  get = (fun (x: cbor_pair) (f: Cs.field_t fields) -> match f with "cbor_pair_fst" -> x.cbor_pair_fst | "cbor_pair_snd" -> x.cbor_pair_snd);
  get_mk = (fun _ _ -> ());
  extensionality = (fun s1 s2 phi -> phi "cbor_pair_fst"; phi "cbor_pair_snd")
}

noextract
let cbor_pair_td : C.typedef cbor_pair = Cs.struct_typedef cbor_pair_struct_def

open Steel.ST.Util

let test (#s: Ghost.erased cbor_case) (p: C.ref cbor_case_td)
: ST (Ghost.erased cbor_case)
    (C.pts_to p s)
    (fun s' -> C.pts_to p s')
    (C.full cbor_case_td s)
    (fun s' -> C.full cbor_case_td s')
= let ps = Cu.union_switch_field0 _ p "cbor_case_int64" (C.scalar U64.t) in
  C.write ps 1729uL;
  Cu.ununion_field p "cbor_case_int64" ps;
  drop (Cu.has_union_field p "cbor_case_int64" _);
  let s' = vpattern_replace (C.pts_to p) in
  Cu.full_union cbor_case_union_def (Ghost.reveal s') "cbor_case_int64"; // FIXME: find a better pattern for that lemma
  return _
