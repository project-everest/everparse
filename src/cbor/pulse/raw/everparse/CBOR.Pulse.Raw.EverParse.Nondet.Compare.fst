module CBOR.Pulse.Raw.EverParse.Nondet.Compare
#lang-pulse
include CBOR.Spec.Raw.Nondet
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Iterator
open LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module U64 = FStar.UInt64
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen
module Valid = CBOR.Spec.Raw.Valid

// === Pure field correspondence lemmas ===

// Stronger version of cbor_raw_match_cases_prop that includes value-level facts
let cbor_raw_match_fields_prop (x: cbor_raw) (y: raw_data_item) : prop =
  match x, y with
  | CBOR_Case_Int v, Int64 m rv ->
    v.cbor_int_type == m /\ v.cbor_int_value == rv.value /\ v.cbor_int_size == rv.size
  | CBOR_Case_Simple sv, Simple sv' -> sv == sv'
  | CBOR_Case_String v, String m len _ ->
    v.cbor_string_type == m /\ v.cbor_string_size == len.size /\ SZ.v (S.len v.cbor_string_ptr) == U64.v len.value
  | CBOR_Case_Array v, Array len _ ->
    v.cbor_array_length_size == len.size /\ SZ.v (IT.mixed_list_length v.cbor_array_ptr) == U64.v len.value
  | CBOR_Case_Map v, Map len _ ->
    v.cbor_map_length_size == len.size /\ SZ.v (IT.mixed_list_length v.cbor_map_ptr) == U64.v len.value
  | CBOR_Case_Tagged v, Tagged tag _ -> v.cbor_tagged_tag == tag
  | CBOR_Case_Tagged_Serialized v, Tagged tag _ -> v.cbor_tagged_serialized_tag == tag
  | _, _ -> False

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

let cbor_raw_match_fields_prop_of_header
  (x: cbor_raw)
  (y: raw_data_item)
  (h: header)
  (_: squash (cbor_raw_get_header x == Some h))
  (_: squash (dfst (synth_raw_data_item_recip y) == h))
: Lemma (cbor_raw_match_fields_prop x y)
= ()

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

```pulse
ghost fn cbor_raw_match_fields
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match pm x y
ensures cbor_raw_match pm x y ** pure (cbor_raw_match_fields_prop x y)
{
  cbor_raw_match_unfold_aux x;
  unfold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  let the_prop = cbor_raw_get_header x ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
  let sq = elim_pure_explicit the_prop;
  cbor_raw_match_fields_prop_of_header x (Ghost.reveal y)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))) sq ();
  intro_pure the_prop sq;
  rewrite
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content cbor_raw_match parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  fold (cbor_raw_match_aux parse_raw_data_item cbor_raw_match pm x (Ghost.reveal y));
  cbor_raw_match_fold_aux x;
  ()
}
```

#pop-options

// === Aux fields helper (parameterized by r) ===
// Analogous to cbor_raw_match_fields, but operates on cbor_raw_match_aux for
// arbitrary r (used with r = cbor_raw_match_fuel (n-1)).

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

ghost fn cbor_raw_match_aux_fields
  (r: perm -> cbor_raw -> raw_data_item -> slprop)
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match_aux parse_raw_data_item r pm x y
ensures cbor_raw_match_aux parse_raw_data_item r pm x y ** pure (cbor_raw_match_fields_prop x y)
{
  unfold (cbor_raw_match_aux parse_raw_data_item r pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content r parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content r parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  let the_prop = cbor_raw_get_header x ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
  let sq = elim_pure_explicit the_prop;
  cbor_raw_match_fields_prop_of_header x (Ghost.reveal y)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))) sq ();
  intro_pure the_prop sq;
  rewrite
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content r parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content r parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  fold (cbor_raw_match_aux parse_raw_data_item r pm x (Ghost.reveal y));
}

#pop-options

// === check_equiv_list decomposition ===

let option_and (x y: option bool) : option bool =
  match x with
  | None -> None
  | Some b -> if b then y else Some false

let option_and_assoc (x y z: option bool)
: Lemma (option_and x (option_and y z) == option_and (option_and x y) z)
= ()

// Decomposition: check_equiv_list (l1 ++ q1) (l2 ++ q2) equiv ==
//   option_and (check_equiv_list l1 l2 equiv) (check_equiv_list q1 q2 equiv)
// when length l1 = length l2 and length q1 = length q2.
// This is the key lemma enabling pairwise iteration over arrays.

#push-options "--z3rlimit 512 --fuel 4 --ifuel 2"

// check_equiv_list_weaken: call check_equiv_list with an equiv whose bound is
// at least as large as list_sum l1 + list_sum l2 (subtyping coercion)
let check_equiv_list_weaken
  (l1 l2: list raw_data_item)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
  (_: squash (list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 <= bound))
: Tot (r: option bool { r == check_equiv_list l1 l2 equiv })
= check_equiv_list l1 l2 equiv

let rec check_equiv_list_decompose
  (l1 l2: list raw_data_item)
  (q1: list raw_data_item)
  (q2: list raw_data_item)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
: Lemma
  (requires
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.length q1 == List.Tot.length q2 /\
    list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 + list_sum raw_data_item_size q1 + list_sum raw_data_item_size q2 <= bound /\
    list_sum raw_data_item_size (List.Tot.append l1 q1) + list_sum raw_data_item_size (List.Tot.append l2 q2) <= bound)
  (ensures
    check_equiv_list (List.Tot.append l1 q1) (List.Tot.append l2 q2) equiv ==
    option_and (check_equiv_list l1 l2 equiv) (check_equiv_list q1 q2 equiv))
  (decreases (list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2))
= list_sum_append raw_data_item_size l1 q1;
  list_sum_append raw_data_item_size l2 q2;
  List.Tot.Properties.append_length l1 q1;
  List.Tot.Properties.append_length l2 q2;
  match l1, l2 with
  | [], [] ->
    List.Tot.Properties.append_l_nil q1;
    List.Tot.Properties.append_l_nil q2
  | a1 :: r1, a2 :: r2 ->
    raw_data_item_size_eq a1;
    raw_data_item_size_eq a2;
    list_sum_append raw_data_item_size r1 q1;
    list_sum_append raw_data_item_size r2 q2;
    List.Tot.Properties.append_length r1 q1;
    List.Tot.Properties.append_length r2 q2;
    check_equiv_list_decompose r1 r2 q1 q2 bound equiv;
    match equiv a1 a2 with
    | None -> ()
    | Some b ->
      if b then ()
      else match a1, a2 with
      | Tagged tag1 b1, Tagged tag2 b2 ->
        if tag1.value <> tag2.value then ()
        else
          check_equiv_list_decompose (b1 :: r1) (b2 :: r2) q1 q2 bound equiv
      | Array len1 ar1, Array len2 ar2 ->
        if len1.value <> len2.value then ()
        else begin
          List.Tot.Properties.append_assoc ar1 r1 q1;
          List.Tot.Properties.append_assoc ar2 r2 q2;
          List.Tot.Properties.append_length ar1 r1;
          List.Tot.Properties.append_length ar2 r2;
          list_sum_append raw_data_item_size ar1 r1;
          list_sum_append raw_data_item_size ar2 r2;
          list_sum_append raw_data_item_size (List.Tot.append ar1 r1) q1;
          list_sum_append raw_data_item_size (List.Tot.append ar2 r2) q2;
          check_equiv_list_decompose (List.Tot.append ar1 r1) (List.Tot.append ar2 r2) q1 q2 bound equiv
        end
      | _ -> ()

#pop-options

// Corollary: cons decomposition
let check_equiv_list_cons
  (a1 a2: raw_data_item)
  (q1: list raw_data_item)
  (q2: list raw_data_item)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
  (_: squash (
    List.Tot.length q1 == List.Tot.length q2 /\
    raw_data_item_size a1 + raw_data_item_size a2 + list_sum raw_data_item_size q1 + list_sum raw_data_item_size q2 <= bound))
: Lemma
  (check_equiv_list (a1 :: q1) (a2 :: q2) equiv ==
    option_and (check_equiv_list [a1] [a2] equiv) (check_equiv_list q1 q2 equiv))
= check_equiv_list_decompose [a1] [a2] q1 q2 bound equiv

// Pure helper to extract tag value from any tagged cbor_raw constructor
let cbor_raw_tag_value (x: cbor_raw) : U64.t =
  match x with
  | CBOR_Case_Tagged v -> v.cbor_tagged_tag.value
  | CBOR_Case_Tagged_Serialized v -> v.cbor_tagged_serialized_tag.value
  | _ -> 0UL

let cbor_raw_tag_value_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (cbor_raw_match_fields_prop x v))
  (_: squash (Tagged? v))
: Lemma (cbor_raw_tag_value x == (Tagged?.tag v).value)
= ()

// Pure lemma: check_equiv for non-Map, non-Array, non-Tagged cases
// (i.e., Int, Simple, String) where data_model returns false
// reduces to structural comparison

// Per-case lemmas for check_equiv reduction on non-Map cases
// These are much simpler for SMT since the constructors are concrete

#push-options "--z3rlimit 256 --fuel 4 --ifuel 4"

let check_equiv_dm_true_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (x1 x2: raw_data_item)
  (_: squash (dm x1 x2 == true))
: Lemma
  (check_equiv dm mb x1 x2 == Some true)
= ()

let check_equiv_int_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (ty1: major_type_uint64_or_neg_int64)
  (v1: raw_uint64)
  (ty2: major_type_uint64_or_neg_int64)
  (v2: raw_uint64)
  (_: squash (dm (Int64 ty1 v1) (Int64 ty2 v2) == false))
: Lemma
  (check_equiv dm mb (Int64 ty1 v1) (Int64 ty2 v2) == Some (ty1 = ty2 && v1.value = v2.value))
= ()

let check_equiv_simple_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (v1 v2: simple_value)
  (_: squash (dm (Simple v1) (Simple v2) == false))
: Lemma
  (check_equiv dm mb (Simple v1) (Simple v2) == Some (v1 = v2))
= ()

let check_equiv_string_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (x1 x2: raw_data_item)
  (_: squash (String? x1 /\ String? x2))
  (_: squash (dm x1 x2 == false))
: Lemma
  (check_equiv dm mb x1 x2 == Some (String?.typ x1 = String?.typ x2 && String?.v x1 = String?.v x2))
= ()

let check_equiv_tagged_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (x1 x2: raw_data_item)
  (_: squash (Tagged? x1 /\ Tagged? x2))
  (_: squash (dm x1 x2 == false))
: Lemma
  (check_equiv dm mb x1 x2 ==
    (if (Tagged?.tag x1).value = (Tagged?.tag x2).value
     then check_equiv dm mb (Tagged?.v x1) (Tagged?.v x2)
     else Some false))
= ()

let check_equiv_array_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (x1 x2: raw_data_item)
  (_: squash (Array? x1 /\ Array? x2))
  (_: squash (dm x1 x2 == false))
: Lemma
  (check_equiv dm mb x1 x2 ==
    (if (Array?.len x1).value = (Array?.len x2).value
     then check_equiv_list (Array?.v x1) (Array?.v x2) (check_equiv_map dm mb)
     else Some false))
= List.Tot.Properties.append_l_nil (Array?.v x1);
  List.Tot.Properties.append_l_nil (Array?.v x2)

let check_equiv_map_map_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (x1 x2: raw_data_item)
  (_: squash (Map? x1 /\ Map? x2))
  (_: squash (dm x1 x2 == false))
: Lemma
  (check_equiv dm mb x1 x2 == check_equiv_map dm mb x1 x2)
= ()

let check_equiv_mismatch_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (x1 x2: raw_data_item)
  (_: squash (dm x1 x2 == false))
  (_: squash (get_major_type x1 <> get_major_type x2))
: Lemma
  (check_equiv dm mb x1 x2 == Some false)
= ()

#pop-options

// Callback type: data_model implementation at the cbor_raw level.
// Given two cbor_raw values with cbor_raw_match, returns bool matching data_model on the underlying raw_data_items.
inline_for_extraction
let impl_data_model_t
  (data_model: (raw_data_item -> raw_data_item -> bool))
=
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt bool
    (cbor_raw_match pm1 x1 v1 **
     cbor_raw_match pm2 x2 v2)
    (fun res ->
      cbor_raw_match pm1 x1 v1 **
      cbor_raw_match pm2 x2 v2 **
      pure (res == data_model v1 v2))

// Wrapper: convert impl_data_model_t (cbor_raw level) to impl_equiv_hd_t (serialized nlist level)
inline_for_extraction
fn impl_data_model_to_equiv_hd
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
: NG.impl_equiv_hd_t data_model
=
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item))
{
  // === Side 1: extract head as cbor_raw ===

  let hd1 = nlist_hd_strong_prefix () (jump_raw_data_item f64) (SZ.v n1) l1;
  let x1 = cbor_raw_read 1.0R f64 hd1;
  Trade.trans _ _
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1);

  // === Side 2: extract head as cbor_raw ===

  let hd2 = nlist_hd_strong_prefix () (jump_raw_data_item f64) (SZ.v n2) l2;
  let x2 = cbor_raw_read 1.0R f64 hd2;
  Trade.trans _ _
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2);

  // === Call data_model callback ===

  let res = impl_dm x1 x2;

  // === Trade back ===

  Trade.elim _ (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2);
  Trade.elim _ (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1);

  res
}

// === Local instance of impl_data_model_t for basic_data_model ===
// basic_data_model is always false, so this is just a constant false.
inline_for_extraction noextract [@@noextract_to "krml"]
fn cbor_nondet_impl_basic_local
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2
returns res: bool
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (res == basic_data_model v1 v2)
{
  false
}

// === Gen-level pipeline: non-recursive check_equiv_map_hd (ih is the recursive callback) ===

inline_for_extraction
let impl_check_equiv_map_hd_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (ih: NG.impl_check_equiv_map_hd_t data_model)
: NG.impl_check_equiv_map_hd_t data_model
= NG.impl_check_equiv_map_hd_body (impl_data_model_to_equiv_hd impl_dm f64) ih

inline_for_extraction
let impl_check_equiv_list_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (ih: NG.impl_check_equiv_map_hd_t data_model)
  (map_bound: option SZ.t)
: NG.impl_check_equiv_list_t (check_equiv_map data_model (NG.option_sz_v map_bound))
= NG.impl_check_equiv_list_map (impl_check_equiv_map_hd_compare impl_dm f64 ih) map_bound

inline_for_extraction
let impl_check_equiv_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (ih: NG.impl_check_equiv_map_hd_t data_model)
  (map_bound: option SZ.t)
: NG.impl_equiv_t #_ (check_equiv data_model (NG.option_sz_v map_bound))
= NG.impl_check_equiv map_bound (impl_check_equiv_list_compare impl_dm f64 ih map_bound)

inline_for_extraction
fn impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (ih: NG.impl_check_equiv_map_hd_t data_model)
  (nl1: SZ.t)
  (l1: S.slice byte)
  (nl2: SZ.t)
  (l2: S.slice byte)
  (#pl1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v nl1) (raw_data_item & raw_data_item)))
  (#pl2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v nl2) (raw_data_item & raw_data_item)))
requires
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl1) (nondep_then parse_raw_data_item parse_raw_data_item)) l1 #pl1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl2) (nondep_then parse_raw_data_item parse_raw_data_item)) l2 #pl2 gl2
returns res: option bool
ensures
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl1) (nondep_then parse_raw_data_item parse_raw_data_item)) l1 #pl1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl2) (nondep_then parse_raw_data_item parse_raw_data_item)) l2 #pl2 gl2 **
  pure (
    res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow (check_equiv data_model None) (check_equiv data_model None) gl1) gl2
  )
{
  NG.impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow (impl_check_equiv_compare impl_dm f64 ih None) nl1 l1 nl2 l2
}

// === Specialized recursive instance: check_equiv_map_hd for basic_data_model ===

fn rec impl_check_equiv_map_hd_basic
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item))
requires
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
  pure (
    SZ.v n1 > 0 /\ SZ.v n2 > 0
  )
returns res: option bool
ensures
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
  PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
  pure (
    SZ.v n1 > 0 /\ SZ.v n2 > 0 /\
    res == (check_equiv_map basic_data_model (NG.option_sz_v map_bound)) (List.Tot.hd gl1) (List.Tot.hd gl2)
  )
{
  impl_check_equiv_map_hd_compare cbor_nondet_impl_basic_local f64 (impl_check_equiv_map_hd_basic f64) map_bound n1 l1 n2 l2
}

// === Type for the recursive comparison function ===

// Fuel-aware variant of compare_cbor_raw_t: operates on cbor_raw_match_fuel n.
// Requires raw_data_item_size of inputs to fit within n.
inline_for_extraction
noextract [@@noextract_to "krml"]
let compare_cbor_raw_fuel_t
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (n: Ghost.erased nat)
=
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt (option bool)
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (raw_data_item_size v1 <= Ghost.reveal n /\
           raw_data_item_size v2 <= Ghost.reveal n))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (res == check_equiv data_model map_bound v1 v2))

// === Helpers for map_bound decrement ===

let option_nat_decrement_safe (mb: option nat) : option nat =
  match mb with
  | None -> None
  | Some 0 -> Some 0 // dummy, never used (Map case returns None for overflow)
  | Some n -> Some (n - 1)

inline_for_extraction
noextract [@@noextract_to "krml"]
let option_sz_decrement_safe (mb: option SZ.t) : option SZ.t =
  match mb with
  | None -> None
  | Some n -> if n = 0sz then Some 0sz else Some (SZ.sub n 1sz)

let option_sz_decrement_safe_v (mb: option SZ.t)
: Lemma (NG.option_sz_v (option_sz_decrement_safe mb) == option_nat_decrement_safe (NG.option_sz_v mb))
= ()

let option_nat_decrement_safe_spec (mb: option nat)
: Lemma
  (requires mb <> Some 0)
  (ensures option_nat_decrement_safe mb == (match mb with None -> None | Some x -> Some (x - 1)))
= ()

// === Extensionality lemmas for check_equiv vs check_equiv_aux ===

let check_equiv_check_equiv_aux_eq
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (bound: nat)
  (x1 x2: raw_data_item)
: Lemma
  (requires raw_data_item_size x1 + raw_data_item_size x2 <= bound)
  (ensures check_equiv dm mb x1 x2 == check_equiv_aux bound (check_equiv_map dm mb) x1 x2)
= ()

// Extensionality for setoid_assoc_eq_with_overflow: when all keys/values in ll and xr have sizes
// fitting within bound, check_equiv and check_equiv_aux agree
let rec setoid_assoc_eq_with_overflow_check_equiv_ext
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (bound: nat)
  (ll: list (raw_data_item & raw_data_item))
  (xr: (raw_data_item & raw_data_item))
: Lemma
  (requires
    list_sum (pair_sum raw_data_item_size raw_data_item_size) ll +
    pair_sum raw_data_item_size raw_data_item_size xr <= bound)
  (ensures
    setoid_assoc_eq_with_overflow (check_equiv dm mb) (check_equiv dm mb) ll xr ==
    setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map dm mb)) (check_equiv_aux bound (check_equiv_map dm mb)) ll xr)
  (decreases ll)
= match ll with
  | [] -> ()
  | (kl, vl) :: ll' ->
    check_equiv_check_equiv_aux_eq dm mb bound (fst xr) kl;
    match check_equiv dm mb (fst xr) kl with
    | None -> ()
    | Some false ->
      setoid_assoc_eq_with_overflow_check_equiv_ext dm mb bound ll' xr
    | Some true ->
      check_equiv_check_equiv_aux_eq dm mb bound (snd xr) vl

// When two functions agree pointwise on list elements, list_for_all_with_overflow agrees
let rec list_for_all_with_overflow_ext
  (#t: Type)
  (f g: t -> option bool)
  (l: list t)
: Lemma
  (requires forall x . List.Tot.memP x l ==> f x == g x)
  (ensures list_for_all_with_overflow f l == list_for_all_with_overflow g l)
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    assert (f a == g a);
    match f a with
    | Some true -> list_for_all_with_overflow_ext f g q
    | _ -> ()

// Combined bridge: list_for_all_with_overflow o setoid_assoc_eq_with_overflow
// with check_equiv dm mb agrees with check_equiv_aux bound (check_equiv_map dm mb)
let check_equiv_map_list_for_all_ext
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (bound: nat)
  (inner outer: list (raw_data_item & raw_data_item))
: Lemma
  (requires
    list_sum (pair_sum raw_data_item_size raw_data_item_size) inner +
    list_sum (pair_sum raw_data_item_size raw_data_item_size) outer <= bound)
  (ensures
    list_for_all_with_overflow
      (setoid_assoc_eq_with_overflow (check_equiv dm mb) (check_equiv dm mb) inner)
      outer
    ==
    list_for_all_with_overflow
      (setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map dm mb)) (check_equiv_aux bound (check_equiv_map dm mb)) inner)
      outer)
= let ext_assoc (xr: (raw_data_item & raw_data_item)) : Lemma
    (requires List.Tot.memP xr outer)
    (ensures
      setoid_assoc_eq_with_overflow (check_equiv dm mb) (check_equiv dm mb) inner xr ==
      setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map dm mb)) (check_equiv_aux bound (check_equiv_map dm mb)) inner xr)
  = list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) outer xr;
    setoid_assoc_eq_with_overflow_check_equiv_ext dm mb bound inner xr
  in
  Classical.forall_intro (Classical.move_requires ext_assoc);
  list_for_all_with_overflow_ext
    (setoid_assoc_eq_with_overflow (check_equiv dm mb) (check_equiv dm mb) inner)
    (setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map dm mb)) (check_equiv_aux bound (check_equiv_map dm mb)) inner)
    outer

// === Body of the recursive comparison function ===

module I16 = FStar.Int16
module Spec = CBOR.Spec.API.Format
module CompareBytes = CBOR.Pulse.Raw.Compare.Bytes

// Coerce Pulse ghost fn to stt_ghost for share_t / gather_t
```pulse
ghost
fn cbor_raw_match_share_wrapper
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
requires cbor_raw_match p x1 x2
ensures cbor_raw_match (p /. 2.0R) x1 x2 ** cbor_raw_match (p /. 2.0R) x1 x2
{
  cbor_raw_match_share x1
}
```

```pulse
ghost
fn cbor_raw_match_gather_wrapper
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
requires cbor_raw_match p x1 x2 ** cbor_raw_match p' x1 x2'
ensures cbor_raw_match (p +. p') x1 x2 ** pure (x2 == x2')
{
  cbor_raw_match_gather x1 #p #x2 #p' #x2'
}
```

let cbor_raw_match_share_t : I.share_t cbor_raw_match = cbor_raw_match_share_wrapper
let cbor_raw_match_gather_t : I.gather_t cbor_raw_match = cbor_raw_match_gather_wrapper

// Map entry vmatch: the vmatch used for map entries in mixed_list_match
let cbor_map_entry_vmatch
  (pm: perm)
  (elem: cbor_map_entry cbor_raw)
  (v: (raw_data_item & raw_data_item))
: Tot slprop
= cbor_map_entry_match cbor_raw_match pm elem v

// Share wrapper for map entry vmatch
```pulse
ghost
fn cbor_map_entry_vmatch_share_wrapper
  (entry: cbor_map_entry cbor_raw) (#pm: perm) (#pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm entry pair
ensures cbor_map_entry_vmatch (pm /. 2.0R) entry pair ** cbor_map_entry_vmatch (pm /. 2.0R) entry pair
{
  unfold (cbor_map_entry_vmatch pm entry pair);
  cbor_map_entry_match_share cbor_raw_match cbor_raw_match_share_t entry;
  fold (cbor_map_entry_vmatch (pm /. 2.0R) entry pair);
  fold (cbor_map_entry_vmatch (pm /. 2.0R) entry pair);
}
```

// Gather wrapper for map entry vmatch
```pulse
ghost
fn cbor_map_entry_vmatch_gather_wrapper
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm) (#pair: (raw_data_item & raw_data_item))
  (#pm': perm) (#pair': (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm entry pair ** cbor_map_entry_vmatch pm' entry pair'
ensures cbor_map_entry_vmatch (pm +. pm') entry pair ** pure (pair == pair')
{
  unfold (cbor_map_entry_vmatch pm entry pair);
  unfold (cbor_map_entry_vmatch pm' entry pair');
  unfold (cbor_map_entry_match cbor_raw_match pm entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd pair));
  unfold (cbor_map_entry_match cbor_raw_match pm' entry pair');
  unfold (vmatch_pair_with_proj (cbor_raw_match pm') cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj) entry pair');
  unfold (vmatch_with_pair_proj (cbor_raw_match pm') cbor_map_entry_value_proj entry (snd pair'));
  rewrite (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match pm entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair'))
       as (cbor_raw_match pm' entry.cbor_map_entry_key (fst pair'));
  rewrite (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match pm entry.cbor_map_entry_value (snd pair));
  rewrite (cbor_raw_match pm' (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair'))
       as (cbor_raw_match pm' entry.cbor_map_entry_value (snd pair'));
  cbor_raw_match_gather entry.cbor_map_entry_key #pm #(fst pair) #pm' #(fst pair');
  cbor_raw_match_gather entry.cbor_map_entry_value #pm #(snd pair) #pm' #(snd pair');
  rewrite (cbor_raw_match (pm +. pm') entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match (pm +. pm') (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match (pm +. pm') entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match (pm +. pm') (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match (pm +. pm')) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match cbor_raw_match (pm +. pm') entry pair);
  fold (cbor_map_entry_vmatch (pm +. pm') entry pair);
}
```

let cbor_map_entry_vmatch_share : I.share_t cbor_map_entry_vmatch = cbor_map_entry_vmatch_share_wrapper
let cbor_map_entry_vmatch_gather : I.gather_t cbor_map_entry_vmatch = cbor_map_entry_vmatch_gather_wrapper

// zero_copy_parse for map entries: read two cbor_raw values from a serialized pair
inline_for_extraction
```pulse
fn cbor_map_entry_zero_copy_parse
  (f64: squash SZ.fits_u64)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
requires PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v
returns res: cbor_map_entry cbor_raw
ensures cbor_map_entry_vmatch 1.0R res v **
        Trade.trade (cbor_map_entry_vmatch 1.0R res v)
                    (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
{
  // Use the nondep_then zero_copy_parse to get a pair of cbor_raw values
  let zcp1 = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read 1.0R f64) ();
  let pair = LowParse.PulseParse.Combinators.zero_copy_parse_nondep_then (jump_raw_data_item f64) zcp1 () zcp1 input;
  let entry : cbor_map_entry cbor_raw = { cbor_map_entry_key = fst pair; cbor_map_entry_value = snd pair };
  // vmatch_pair (cbor_raw_match 1.0R) (cbor_raw_match 1.0R) pair v
  //   = cbor_raw_match 1.0R (fst pair) (fst v) ** cbor_raw_match 1.0R (snd pair) (snd v)
  // cbor_map_entry_vmatch 1.0R entry v
  //   = cbor_map_entry_match cbor_raw_match 1.0R entry v
  //   = cbor_raw_match 1.0R entry.key (fst v) ** cbor_raw_match 1.0R entry.value (snd v)
  // These are definitionally equal since entry.key = fst pair, entry.value = snd pair
  rewrite (vmatch_pair (cbor_raw_match 1.0R) (cbor_raw_match 1.0R) pair (Ghost.reveal v))
       as (cbor_map_entry_vmatch 1.0R entry v);
  rewrite (Trade.trade (vmatch_pair (cbor_raw_match 1.0R) (cbor_raw_match 1.0R) pair (Ghost.reveal v))
                       (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v))
       as (Trade.trade (cbor_map_entry_vmatch 1.0R entry v)
                       (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v));
  entry
}
```

// Helper: unfold cbor_map_entry_vmatch to expose key and value cbor_raw_match
```pulse
ghost
fn unfold_map_entry_vmatch
  (pm: perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch pm entry pair
ensures cbor_raw_match pm entry.cbor_map_entry_key (fst pair) **
        cbor_raw_match pm entry.cbor_map_entry_value (snd pair)
{
  unfold (cbor_map_entry_vmatch pm entry pair);
  unfold (cbor_map_entry_match cbor_raw_match pm entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd pair));
  rewrite (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match pm entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match pm entry.cbor_map_entry_value (snd pair));
}
```

// Helper: fold cbor_raw_match for key and value back into cbor_map_entry_vmatch
```pulse
ghost
fn fold_map_entry_vmatch
  (pm: perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: (raw_data_item & raw_data_item))
requires cbor_raw_match pm entry.cbor_map_entry_key (fst pair) **
         cbor_raw_match pm entry.cbor_map_entry_value (snd pair)
ensures cbor_map_entry_vmatch pm entry pair
{
  rewrite (cbor_raw_match pm entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match pm entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match cbor_raw_match pm entry pair);
  fold (cbor_map_entry_vmatch pm entry pair);
}
```

// Fuel-aware variant of compare_cbor_raw_fn_t: operates on cbor_raw_match_fuel n.
// Requires raw_data_item_size of inputs to fit within n.
inline_for_extraction
noextract [@@noextract_to "krml"]
let compare_cbor_raw_fn_fuel_t
  (n: Ghost.erased nat)
  (equiv: raw_data_item -> raw_data_item -> option bool)
=
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt (option bool)
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (raw_data_item_size v1 <= Ghost.reveal n /\
           raw_data_item_size v2 <= Ghost.reveal n))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (res == equiv v1 v2))

// Fuel-aware variant of impl_data_model_t: operates on cbor_raw_match_fuel n.
// Used by compare_cbor_raw_fuel so that the data_model callback can run on
// the fuel-indexed match without needing a fuel-to-non-fuel bridge.
inline_for_extraction
noextract [@@noextract_to "krml"]
let impl_data_model_fuel_t
  (n: Ghost.erased nat)
  (data_model: (raw_data_item -> raw_data_item -> bool))
=
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt bool
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2)
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (res == data_model v1 v2))

// Fuel-aware variant of compare_cbor_raw_setoid_assoc_eq: operates on cbor_raw_match_fuel n.
// Requires that map_entries' total pair size and xr_pair's component sizes all fit in n,
// so that calls to compare_impl (which has a size precondition) typecheck.
#push-options "--z3rlimit 512 --fuel 4 --ifuel 4 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_setoid_assoc_eq_fuel
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (#equiv: Ghost.erased (raw_data_item -> raw_data_item -> option bool))
  (compare_impl: compare_cbor_raw_fn_fuel_t n equiv)
  (f64: squash SZ.fits_u64)
  (map_ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (#pm_map: perm)
  (#map_entries: Ghost.erased (list (raw_data_item & raw_data_item)))
  (xr: cbor_map_entry cbor_raw)
  (#pm_xr: perm)
  (#xr_pair: Ghost.erased (raw_data_item & raw_data_item))
requires
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_map map_ml map_entries **
  cbor_map_entry_vmatch_fuel n pm_xr xr xr_pair **
  pure (
    list_sum (pair_sum raw_data_item_size raw_data_item_size) map_entries <= Ghost.reveal n /\
    raw_data_item_size (fst (Ghost.reveal xr_pair)) <= Ghost.reveal n /\
    raw_data_item_size (snd (Ghost.reveal xr_pair)) <= Ghost.reveal n
  )
returns res: option bool
ensures
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_map map_ml map_entries **
  cbor_map_entry_vmatch_fuel n pm_xr xr xr_pair **
  pure (res == setoid_assoc_eq_with_overflow equiv equiv map_entries xr_pair)
{
  let zcp = cbor_map_entry_zero_copy_parse_fuel n 1.0R f64;
  let len = IT.mixed_list_length map_ml;
  // Establish length invariant
  I.mixed_list_match_length (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_map map_ml (Ghost.reveal map_entries);
  // Start iterator on map_entries
  let it_init = I.iterator_start (cbor_map_entry_vmatch_fuel n)
    (nondep_then parse_raw_data_item parse_raw_data_item) (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64)) pm_map map_ml map_entries
    (cbor_map_entry_vmatch_fuel_share_t n) (cbor_map_entry_vmatch_fuel_gather_t n);
  // Set up loop state: r_done = None means "keep searching", Some r means "done with result r"
  let mut r_it = it_init;
  let mut r_done : option (option bool) = None #(option bool);
  let mut r_cnt = 0sz;
  // While loop: iterate through map_entries searching for matching key
  while (
    let done = !r_done;
    let cnt = !r_cnt;
    (None? done && SZ.lt cnt len)
  ) invariant exists* it_c done_c cnt_c rem pm_c .
    R.pts_to r_it it_c **
    R.pts_to r_done done_c **
    R.pts_to r_cnt cnt_c **
    I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_c it_c rem **
    Trade.trade
      (I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_c it_c rem)
      (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_map map_ml map_entries) **
    cbor_map_entry_vmatch_fuel n pm_xr xr xr_pair **
    pure (
      SZ.v cnt_c <= SZ.v len /\
      List.Tot.length rem == SZ.v len - SZ.v cnt_c /\
      list_sum (pair_sum raw_data_item_size raw_data_item_size) rem <=
        list_sum (pair_sum raw_data_item_size raw_data_item_size) map_entries /\
      setoid_assoc_eq_with_overflow equiv equiv map_entries xr_pair ==
        (match done_c with
         | Some r -> r
         | None -> setoid_assoc_eq_with_overflow equiv equiv rem xr_pair)
    )
  {
    // Get next entry from iterator
    let e = I.iterator_next (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
      (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64)) _ r_it _ _
      (cbor_map_entry_vmatch_fuel_share_t n) (cbor_map_entry_vmatch_fuel_gather_t n) zcp;
    unfold (I.iterator_next_post (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) _ r_it _ _ e);
    with pmv hdv tl itn pmn . assert (
      cbor_map_entry_vmatch_fuel n pmv e hdv **
      R.pts_to r_it itn **
      I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pmn itn tl
    );
    Trade.trans _ _
      (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_map map_ml map_entries);
    // Unfold both entries to access keys and values
    cbor_map_entry_vmatch_fuel_elim n e;
    cbor_map_entry_vmatch_fuel_elim n xr;
    // Compare keys
    let key_res = compare_impl xr.cbor_map_entry_key e.cbor_map_entry_key;
    match key_res {
      None -> {
        // Overflow: result is None
        cbor_map_entry_vmatch_fuel_intro n e pmv hdv;
        cbor_map_entry_vmatch_fuel_intro n xr pm_xr xr_pair;
        Trade.elim_hyp_l _ _
          (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
            pm_map map_ml map_entries);
        r_done := Some (None #bool);
        let c = !r_cnt;
        r_cnt := SZ.add c 1sz;
      }
      Some key_match -> {
        if key_match {
          // Keys match: compare values
          let val_res = compare_impl xr.cbor_map_entry_value e.cbor_map_entry_value;
          cbor_map_entry_vmatch_fuel_intro n e pmv hdv;
          cbor_map_entry_vmatch_fuel_intro n xr pm_xr xr_pair;
          Trade.elim_hyp_l _ _
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
              pm_map map_ml map_entries);
          r_done := Some val_res;
          let c = !r_cnt;
          r_cnt := SZ.add c 1sz;
        } else {
          // Keys don't match: continue searching
          cbor_map_entry_vmatch_fuel_intro n e pmv hdv;
          cbor_map_entry_vmatch_fuel_intro n xr pm_xr xr_pair;
          Trade.elim_hyp_l _ _
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
              pm_map map_ml map_entries);
          let c = !r_cnt;
          r_cnt := SZ.add c 1sz;
        }
      }
    }
  };
  // After loop: trade back to restore mixed_list_match
  Trade.elim _ (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_map map_ml map_entries);
  let done = !r_done;
  match done {
    Some r -> { r }
    None -> { Some false }
  }
}
```

#pop-options

// Fuel-aware variant of compare_cbor_raw_list_for_all: operates on cbor_raw_match_fuel n.
// Requires that both inner_entries' and outer_entries' total pair sizes fit in n,
// so the inner setoid_assoc_eq_fuel call typechecks for each popped outer entry.
#push-options "--z3rlimit 512 --fuel 4 --ifuel 4 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_list_for_all_fuel
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (#equiv: Ghost.erased (raw_data_item -> raw_data_item -> option bool))
  (compare_impl: compare_cbor_raw_fn_fuel_t n equiv)
  (f64: squash SZ.fits_u64)
  (inner_ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (#pm_inner: perm)
  (#inner_entries: Ghost.erased (list (raw_data_item & raw_data_item)))
  (outer_ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (#pm_outer: perm)
  (#outer_entries: Ghost.erased (list (raw_data_item & raw_data_item)))
requires
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_inner inner_ml inner_entries **
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_outer outer_ml outer_entries **
  pure (
    list_sum (pair_sum raw_data_item_size raw_data_item_size) inner_entries <= Ghost.reveal n /\
    list_sum (pair_sum raw_data_item_size raw_data_item_size) outer_entries <= Ghost.reveal n
  )
returns res: option bool
ensures
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_inner inner_ml inner_entries **
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_outer outer_ml outer_entries **
  pure (res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv inner_entries) outer_entries)
{
  let zcp = cbor_map_entry_zero_copy_parse_fuel n 1.0R f64;
  let len = IT.mixed_list_length outer_ml;
  // Establish length invariant
  I.mixed_list_match_length (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_outer outer_ml (Ghost.reveal outer_entries);
  // Start iterator on outer_entries
  let it_init = I.iterator_start (cbor_map_entry_vmatch_fuel n)
    (nondep_then parse_raw_data_item parse_raw_data_item) (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64)) pm_outer outer_ml outer_entries
    (cbor_map_entry_vmatch_fuel_share_t n) (cbor_map_entry_vmatch_fuel_gather_t n);
  let mut r_it = it_init;
  let mut r_done : option (option bool) = None #(option bool);
  let mut r_cnt = 0sz;
  while (
    let done = !r_done;
    let cnt = !r_cnt;
    (None? done && SZ.lt cnt len)
  ) invariant exists* it_c done_c cnt_c rem pm_c .
    R.pts_to r_it it_c **
    R.pts_to r_done done_c **
    R.pts_to r_cnt cnt_c **
    I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_c it_c rem **
    Trade.trade
      (I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_c it_c rem)
      (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_outer outer_ml outer_entries) **
    I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
      pm_inner inner_ml inner_entries **
    pure (
      SZ.v cnt_c <= SZ.v len /\
      List.Tot.length rem == SZ.v len - SZ.v cnt_c /\
      list_sum (pair_sum raw_data_item_size raw_data_item_size) rem <=
        list_sum (pair_sum raw_data_item_size raw_data_item_size) outer_entries /\
      list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv inner_entries) outer_entries ==
        (match done_c with
         | Some r -> r
         | None -> list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv inner_entries) rem)
    )
  {
    // Get next entry from iterator
    let e = I.iterator_next (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
      (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64)) _ r_it _ _
      (cbor_map_entry_vmatch_fuel_share_t n) (cbor_map_entry_vmatch_fuel_gather_t n) zcp;
    unfold (I.iterator_next_post (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) _ r_it _ _ e);
    with pmv hdv tl itn pmn . assert (
      cbor_map_entry_vmatch_fuel n pmv e hdv **
      R.pts_to r_it itn **
      I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pmn itn tl
    );
    Trade.trans _ _
      (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_outer outer_ml outer_entries);
    // Call setoid_assoc_eq_fuel on this entry against the inner map.
    // Size preconditions follow from iterator_next_post's pure fact rem == hdv :: tl and the
    // invariant list_sum (pair) rem <= list_sum (pair) outer_entries <= n.
    let entry_res = compare_cbor_raw_setoid_assoc_eq_fuel n compare_impl f64 inner_ml e;
    match entry_res {
      Some b -> {
        if b {
          // Some true: this entry matched, continue searching
          Trade.elim_hyp_l _ _
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
              pm_outer outer_ml outer_entries);
          let c = !r_cnt;
          r_cnt := SZ.add c 1sz;
        } else {
          // Some false: entry not found, stop
          Trade.elim_hyp_l _ _
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
              pm_outer outer_ml outer_entries);
          r_done := Some (Some false);
          let c = !r_cnt;
          r_cnt := SZ.add c 1sz;
        }
      }
      None -> {
        // Overflow: stop
        Trade.elim_hyp_l _ _
          (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
            pm_outer outer_ml outer_entries);
        r_done := Some (None #bool);
        let c = !r_cnt;
        r_cnt := SZ.add c 1sz;
      }
    }
  };
  // After loop: trade back to restore outer mixed_list_match
  Trade.elim _ (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_outer outer_ml outer_entries);
  let done = !r_done;
  match done {
    Some r -> { r }
    None -> { Some true }
  }
}
```

#pop-options

#push-options "--z3rlimit 512 --fuel 4 --ifuel 4 --split_queries always"

// Fuel-aware variant of compare_cbor_raw_array_case.
//
// Uses Strategy A: instead of an n>=2 squash for non-empty arrays, we propagate a
// raw_data_item_size v1/v2 <= n precondition through the type. For non-empty arrays
// `Array _ (cons _ _)`, raw_data_item_size_eq gives size = 2 + list_sum size ar1 >= 3,
// so n >= 3 and hence n - 1 >= 2 suffices for cbor_raw_read_fuel. The loop invariant
// also tracks list_sum size rem1/rem2 <= list_sum size ar1/ar2 so that each popped
// element hdv has size hdv <= n - 2 <= n - 1 for the compare_rec call.
inline_for_extraction
fn compare_cbor_raw_array_case_fuel
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (compare_rec: compare_cbor_raw_fuel_t data_model (NG.option_sz_v map_bound) (Ghost.hide (Ghost.reveal n - 1)))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (_: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (
    Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
    List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
    raw_data_item_size v1 <= Ghost.reveal n /\
    raw_data_item_size v2 <= Ghost.reveal n /\
    check_equiv data_model (NG.option_sz_v map_bound) v1 v2 ==
      check_equiv_list (Array?.v (Ghost.reveal v1)) (Array?.v (Ghost.reveal v2)) (check_equiv_map data_model (NG.option_sz_v map_bound))
  )
returns res: option bool
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (res == check_equiv data_model (NG.option_sz_v map_bound) v1 v2)
{
  if (len = 0sz) {
    // Both arrays empty: check_equiv_list [] [] _ == Some true (by reduction).
    // The precondition gives us check_equiv ... == check_equiv_list (Array?.v v1) (Array?.v v2) _
    // and length (Array?.v v1) == 0 ⟹ Array?.v v1 == [], same for v2.
    Some true
  } else {
    // len > 0, so by raw_data_item_size_eq and non-empty Array?.v, size v1 >= 3, hence n >= 3,
    // hence n - 1 >= 2. We invoke raw_data_item_size_eq explicitly to give Z3 the unfolding.
    raw_data_item_size_eq v1;
    raw_data_item_size_eq v2;
    let n1 : Ghost.erased nat = Ghost.hide (Ghost.reveal n - 1);
    // Unfold cbor_raw_match_fuel n on both sides to cbor_raw_match_aux
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_fuel n pm1 x1 v1)
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
    rewrite (cbor_raw_match_fuel n pm2 x2 v2)
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);

    let zcp = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read_fuel n1 1.0R f64) ();

    // --- Side 1: get array, build trade chain ending at cbor_raw_match_fuel n ---
    let ar_ml1 = cbor_raw_get_array_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
    with pm1_a ar1 . assert (
      I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1_a ar_ml1 ar1 **
      trade (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1_a ar_ml1 ar1)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
    );
    intro
      (trade
        (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
        (cbor_raw_match_fuel n pm1 x1 v1))
      #emp
      fn _ {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1)
      };
    Trade.trans
      (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1_a ar_ml1 ar1)
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
      (cbor_raw_match_fuel n pm1 x1 v1);

    // --- Side 2: same as side 1 ---
    let ar_ml2 = cbor_raw_get_array_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
    with pm2_a ar2 . assert (
      I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2_a ar_ml2 ar2 **
      trade (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2_a ar_ml2 ar2)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
    );
    intro
      (trade
        (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
        (cbor_raw_match_fuel n pm2 x2 v2))
      #emp
      fn _ {
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2)
      };
    Trade.trans
      (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2_a ar_ml2 ar2)
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
      (cbor_raw_match_fuel n pm2 x2 v2);

    // Start iterators
    let it1_init = I.iterator_start
      (cbor_raw_match_fuel (n - 1))
      parse_raw_data_item (jump_raw_data_item f64)
      pm1_a ar_ml1 ar1
      (cbor_raw_match_fuel_share_t (n - 1))
      (cbor_raw_match_fuel_gather_t (n - 1));
    Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);
    let it2_init = I.iterator_start
      (cbor_raw_match_fuel (n - 1))
      parse_raw_data_item (jump_raw_data_item f64)
      pm2_a ar_ml2 ar2
      (cbor_raw_match_fuel_share_t (n - 1))
      (cbor_raw_match_fuel_gather_t (n - 1));
    Trade.trans _ _ (cbor_raw_match_fuel n pm2 x2 v2);

    let mut r_it1 = it1_init;
    let mut r_it2 = it2_init;
    let mut r_acc : option bool = Some true;
    let mut r_cnt = 0sz;

    while (
      let acc = !r_acc;
      let cnt = !r_cnt;
      (SZ.lt cnt len && acc = Some true)
    ) invariant exists* it1c it2c acc_c cnt_c rem1 rem2 pm1c pm2c .
      R.pts_to r_it1 it1c **
      R.pts_to r_it2 it2c **
      R.pts_to r_acc acc_c **
      R.pts_to r_cnt cnt_c **
      I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1c it1c rem1 **
      I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2c it2c rem2 **
      trade (I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1c it1c rem1)
            (cbor_raw_match_fuel n pm1 x1 v1) **
      trade (I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2c it2c rem2)
            (cbor_raw_match_fuel n pm2 x2 v2) **
      pure (
        SZ.v cnt_c <= SZ.v len /\
        List.Tot.length rem1 == SZ.v len - SZ.v cnt_c /\
        List.Tot.length rem2 == SZ.v len - SZ.v cnt_c /\
        Ghost.reveal ar1 == Array?.v (Ghost.reveal v1) /\
        Ghost.reveal ar2 == Array?.v (Ghost.reveal v2) /\
        list_sum raw_data_item_size rem1 <= list_sum raw_data_item_size (Ghost.reveal ar1) /\
        list_sum raw_data_item_size rem2 <= list_sum raw_data_item_size (Ghost.reveal ar2) /\
        list_sum raw_data_item_size rem1 + list_sum raw_data_item_size rem2 <= list_sum raw_data_item_size (Ghost.reveal ar1) + list_sum raw_data_item_size (Ghost.reveal ar2) /\
        check_equiv_list (Ghost.reveal ar1) (Ghost.reveal ar2) (check_equiv_map data_model (NG.option_sz_v map_bound)) ==
          option_and acc_c (check_equiv_list rem1 rem2 (check_equiv_map data_model (NG.option_sz_v map_bound)))
      )
    {
      let e1 = I.iterator_next (cbor_raw_match_fuel (n - 1)) parse_raw_data_item (jump_raw_data_item f64) _ r_it1 _ _
        (cbor_raw_match_fuel_share_t (n - 1)) (cbor_raw_match_fuel_gather_t (n - 1)) zcp;
      unfold (I.iterator_next_post (cbor_raw_match_fuel (n - 1)) parse_raw_data_item _ r_it1 _ _ e1);
      with pmv1 hdv1 tl1 it1n pm1n . assert (
        cbor_raw_match_fuel (n - 1) pmv1 e1 hdv1 **
        R.pts_to r_it1 it1n **
        I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1n it1n tl1
      );
      Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);
      let e2 = I.iterator_next (cbor_raw_match_fuel (n - 1)) parse_raw_data_item (jump_raw_data_item f64) _ r_it2 _ _
        (cbor_raw_match_fuel_share_t (n - 1)) (cbor_raw_match_fuel_gather_t (n - 1)) zcp;
      unfold (I.iterator_next_post (cbor_raw_match_fuel (n - 1)) parse_raw_data_item _ r_it2 _ _ e2);
      with pmv2 hdv2 tl2 it2n pm2n . assert (
        cbor_raw_match_fuel (n - 1) pmv2 e2 hdv2 **
        R.pts_to r_it2 it2n **
        I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2n it2n tl2
      );
      Trade.trans _ _ (cbor_raw_match_fuel n pm2 x2 v2);
      let pair_res = compare_rec e1 e2;
      Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
      Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
      let old_acc = !r_acc;
      let old_cnt = !r_cnt;
      r_acc := option_and old_acc pair_res;
      r_cnt := SZ.add old_cnt 1sz;
      check_equiv_list_cons (Ghost.reveal hdv1) (Ghost.reveal hdv2) (Ghost.reveal tl1) (Ghost.reveal tl2)
        (list_sum raw_data_item_size (Ghost.reveal ar1) + list_sum raw_data_item_size (Ghost.reveal ar2))
        (check_equiv_map data_model (NG.option_sz_v map_bound)) ();
      check_equiv_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal hdv1) (Ghost.reveal hdv2);
      option_and_assoc old_acc pair_res
        (check_equiv_list (Ghost.reveal tl1) (Ghost.reveal tl2) (check_equiv_map data_model (NG.option_sz_v map_bound)));
    };
    Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
    Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
    !r_acc
  }
}

// === Phase 5: Fuel-aware recursive comparison function ===
//
// Dispatches by major type using cbor_raw_match_fuel n throughout, with per-case
// lemmas mirroring the spec function check_equiv.
//
// Strategy A: a raw_data_item_size v <= n precondition propagated through the type
// guarantees that, in the Tagged/Array/Map cases, n is large enough (n >= 2 for empty
// Array/Map/Tagged with empty content, n >= 3 for non-empty Array/Map/Tagged with
// non-empty content). This is enough for the recursive sub-calls at fuel n - 1 to
// satisfy their own size preconditions (size of any sub-item <= n - 1).
//
// impl_dm is taken at the fuel-aware type (impl_data_model_fuel_t n data_model) so
// the data_model can be invoked directly on the fuel-indexed match.
inline_for_extraction
```pulse
fn compare_cbor_raw_fuel
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (impl_dm: impl_data_model_fuel_t n data_model)
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (compare_rec: compare_cbor_raw_fuel_t data_model (NG.option_sz_v map_bound) (Ghost.hide (Ghost.reveal n - 1)))
  (compare_rec_map: compare_cbor_raw_fuel_t data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)) (Ghost.hide (Ghost.reveal n - 1)))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (raw_data_item_size v1 <= Ghost.reveal n /\
        raw_data_item_size v2 <= Ghost.reveal n)
returns res: option bool
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (res == check_equiv data_model (NG.option_sz_v map_bound) v1 v2)
{
  // Step 1: Try data_model first
  let dm_res = impl_dm x1 x2;
  if dm_res {
    check_equiv_dm_true_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) ();
    Some true
  } else {
    // Step 2: Unfold cbor_raw_match_fuel n on both sides to cbor_raw_match_aux
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_fuel n pm1 x1 v1)
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
    rewrite (cbor_raw_match_fuel n pm2 x2 v2)
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
    // Expose raw_data_item_size unfolding for sub-call size preconditions.
    raw_data_item_size_eq v1;
    raw_data_item_size_eq v2;
    // Get cases and fields props on both sides
    cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm1 x1;
    cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm2 x2;
    cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm1 x1;
    cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm2 x2;
    let mt1 = cbor_raw_get_major_type_aux (cbor_raw_match_fuel (n - 1)) pm1 x1;
    let mt2 = cbor_raw_get_major_type_aux (cbor_raw_match_fuel (n - 1)) pm2 x2;
    if (mt1 <> mt2) {
      // Different major types: mismatch
      check_equiv_mismatch_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      // Refold to cbor_raw_match_fuel n
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      Some false
    } else if (mt1 = Spec.cbor_major_type_simple_value) {
      // Simple/Simple: compare values via fields_prop
      let sv1 = CBOR_Case_Simple?.v x1;
      let sv2 = CBOR_Case_Simple?.v x2;
      let res = sv1 = sv2;
      check_equiv_simple_eq data_model (NG.option_sz_v map_bound) sv1 sv2 ();
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      Some res
    } else if (mt1 = Spec.cbor_major_type_uint64 || mt1 = Spec.cbor_major_type_neg_int64) {
      // Int/Int: compare type + value via fields_prop
      let vi1 = CBOR_Case_Int?.v x1;
      let vi2 = CBOR_Case_Int?.v x2;
      let res = vi1.cbor_int_type = vi2.cbor_int_type && (vi1.cbor_int_value <: U64.t) = (vi2.cbor_int_value <: U64.t);
      check_equiv_int_eq data_model (NG.option_sz_v map_bound) vi1.cbor_int_type { size = vi1.cbor_int_size; value = vi1.cbor_int_value } vi2.cbor_int_type { size = vi2.cbor_int_size; value = vi2.cbor_int_value } ();
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      Some res
    } else if (mt1 = Spec.cbor_major_type_byte_string || mt1 = Spec.cbor_major_type_text_string) {
      // String/String: compare type + bytes
      let vs1 = CBOR_Case_String?.v x1;
      let vs2 = CBOR_Case_String?.v x2;
      if (vs1.cbor_string_type <> vs2.cbor_string_type) {
        check_equiv_string_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        Some false
      } else {
        let s1 = cbor_raw_get_string_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
        let s2 = cbor_raw_get_string_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
        let cmp = CompareBytes.lex_compare_bytes s1 s2;
        CBOR.Spec.Raw.Format.bytes_lex_compare_equal (String?.v (Ghost.reveal v1)) (String?.v (Ghost.reveal v2));
        check_equiv_string_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
        Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
        Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        let res = cmp = 0s;
        Some res
      }
    } else if (mt1 = Spec.cbor_major_type_tagged) {
      // Tagged/Tagged: compare tags, recurse on payloads.
      // From SMTpat raw_data_item_size v1 = 2 + size payload1, so n >= 3 and n - 1 >= 2.
      check_equiv_tagged_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      let tag1 = cbor_raw_tag_value x1;
      let tag2 = cbor_raw_tag_value x2;
      cbor_raw_tag_value_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_tag_value_eq x2 (Ghost.reveal v2) () ();
      if (tag1 <> tag2) {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        Some false
      } else {
        let n1 : Ghost.erased nat = Ghost.hide (Ghost.reveal n - 1);
        // Extract payload via _aux accessor; the reader is at fuel n - 1.
        let payload1 = cbor_raw_get_tagged_payload_aux (cbor_raw_match_fuel (n - 1)) pm1
                         (cbor_raw_read_fuel n1 pm1 f64) x1 ();
        let payload2 = cbor_raw_get_tagged_payload_aux (cbor_raw_match_fuel (n - 1)) pm2
                         (cbor_raw_read_fuel n1 pm2 f64) x2 ();
        // Recursive call at fuel n - 1: size of payload = size of v - 2 <= n - 2 <= n - 1
        let res = compare_rec payload1 payload2;
        Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
        Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        res
      }
    } else if (mt1 = Spec.cbor_major_type_array) {
      // Array/Array: compare lengths, then delegate element comparison to Phase 2.
      check_equiv_array_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      let len1 = IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr;
      let len2 = IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr;
      if (len1 <> len2) {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        Some false
      } else {
        // Same length: refold to cbor_raw_match_fuel n, then delegate to Phase 2.
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        compare_cbor_raw_array_case_fuel f64 map_bound n compare_rec x1 x2 len1 ()
      }
    } else {
      // Map/Map: bidirectional setoid_assoc_eq check via Phase 4 (twice).
      check_equiv_map_map_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      match map_bound {
        Some mb_v -> {
          if (mb_v = 0sz) {
            // Overflow: map_bound = Some 0
            cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
            cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
            rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
                 as (cbor_raw_match_fuel n pm1 x1 v1);
            rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
                 as (cbor_raw_match_fuel n pm2 x2 v2);
            None #bool
          } else {
            option_nat_decrement_safe_spec (NG.option_sz_v map_bound);
            // Get both maps at fuel n - 1
            let map_ml1 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
            with pm1_m map1_entries . assert (
              I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries **
              Trade.trade
                (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
            );
            // Rewrite to cbor_map_entry_vmatch_fuel (n - 1)
            rewrite
              (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
              as (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries);
            rewrite
              (Trade.trade
                (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1))
              as (Trade.trade
                (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1));
            // Build trade (cbor_raw_match_aux) (cbor_raw_match_fuel n) closure for side 1
            intro
              (trade
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
                (cbor_raw_match_fuel n pm1 x1 v1))
              #emp
              fn _ {
                cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
                rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
                     as (cbor_raw_match_fuel n pm1 x1 v1)
              };
            Trade.trans
              (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
              (cbor_raw_match_fuel n pm1 x1 v1);

            // Same for side 2
            let map_ml2 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
            with pm2_m map2_entries . assert (
              I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries **
              Trade.trade
                (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
            );
            rewrite
              (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
              as (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries);
            rewrite
              (Trade.trade
                (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2))
              as (Trade.trade
                (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2));
            intro
              (trade
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
                (cbor_raw_match_fuel n pm2 x2 v2))
              #emp
              fn _ {
                cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
                rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
                     as (cbor_raw_match_fuel n pm2 x2 v2)
              };
            Trade.trans
              (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
              (cbor_raw_match_fuel n pm2 x2 v2);

            // Forward check: v1 entries searched against v2 (Phase 4 at fuel n - 1).
            // Inline the fuel argument so it matches the slprop's `(n - 1)` syntactically.
            let fwd = compare_cbor_raw_list_for_all_fuel (Ghost.hide (Ghost.reveal n - 1))
                        #(check_equiv data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)))
                        compare_rec_map f64
                        map_ml2 map_ml1;
            check_equiv_map_list_for_all_ext data_model (option_nat_decrement_safe (NG.option_sz_v map_bound))
              (list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v1)) + list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v2)))
              (Ghost.reveal map2_entries) (Ghost.reveal map1_entries);
            match fwd {
              Some fwd_b -> {
                if fwd_b {
                  let bwd = compare_cbor_raw_list_for_all_fuel (Ghost.hide (Ghost.reveal n - 1))
                              #(check_equiv data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)))
                              compare_rec_map f64
                              map_ml1 map_ml2;
                  check_equiv_map_list_for_all_ext data_model (option_nat_decrement_safe (NG.option_sz_v map_bound))
                    (list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v1)) + list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v2)))
                    (Ghost.reveal map1_entries) (Ghost.reveal map2_entries);
                  Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
                  Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
                  check_equiv_map_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
                  bwd
                } else {
                  Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
                  Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
                  check_equiv_map_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
                  Some false
                }
              }
              None -> {
                Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
                Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
                check_equiv_map_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
                None #bool
              }
            }
          }
        }
        None -> {
          // No bound: proceed with map comparison
          option_nat_decrement_safe_spec (NG.option_sz_v map_bound);
          let map_ml1 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
          with pm1_m map1_entries . assert (
            I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries **
            Trade.trade
              (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
          );
          rewrite
            (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
            as (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries);
          rewrite
            (Trade.trade
              (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1))
            as (Trade.trade
              (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1));
          intro
            (trade
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
              (cbor_raw_match_fuel n pm1 x1 v1))
            #emp
            fn _ {
              cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
              rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
                   as (cbor_raw_match_fuel n pm1 x1 v1)
            };
          Trade.trans
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
            (cbor_raw_match_fuel n pm1 x1 v1);

          let map_ml2 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
          with pm2_m map2_entries . assert (
            I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries **
            Trade.trade
              (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
          );
          rewrite
            (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
            as (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries);
          rewrite
            (Trade.trade
              (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2))
            as (Trade.trade
              (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2));
          intro
            (trade
              (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
              (cbor_raw_match_fuel n pm2 x2 v2))
            #emp
            fn _ {
              cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
              rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
                   as (cbor_raw_match_fuel n pm2 x2 v2)
            };
          Trade.trans
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
            (cbor_raw_match_fuel n pm2 x2 v2);

          let fwd = compare_cbor_raw_list_for_all_fuel (Ghost.hide (Ghost.reveal n - 1))
                      #(check_equiv data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)))
                      compare_rec_map f64
                      map_ml2 map_ml1;
          check_equiv_map_list_for_all_ext data_model (option_nat_decrement_safe (NG.option_sz_v map_bound))
            (list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v1)) + list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v2)))
            (Ghost.reveal map2_entries) (Ghost.reveal map1_entries);
          match fwd {
            Some fwd_b -> {
              if fwd_b {
                let bwd = compare_cbor_raw_list_for_all_fuel (Ghost.hide (Ghost.reveal n - 1))
                            #(check_equiv data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)))
                            compare_rec_map f64
                            map_ml1 map_ml2;
                check_equiv_map_list_for_all_ext data_model (option_nat_decrement_safe (NG.option_sz_v map_bound))
                  (list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v1)) + list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v2)))
                  (Ghost.reveal map1_entries) (Ghost.reveal map2_entries);
                Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
                Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
                check_equiv_map_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
                bwd
              } else {
                Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
                Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
                check_equiv_map_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
                Some false
              }
            }
            None -> {
              Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
              check_equiv_map_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
              None #bool
            }
          }
        }
      }
    }
  }
}
```

#pop-options

// === Phase 6: fuel-aware recursive comparison tying the knot at fuel n ===
//
// Mirrors Det.Compare's impl_cbor_compare_fuel: a Pulse `fn rec` on fuel n that
// recurses with fuel n - 1 via two inline `fn` closures (one for the standard
// recursion at the current map_bound, one for the map-side recursion at the
// decremented map_bound). The closures package the recursive call so we can pass
// them as values of type compare_cbor_raw_fuel_t to compare_cbor_raw_fuel.
// Inside the closure for the map-decremented recursion, the closure's post talks
// about NG.option_sz_v mb_dec while compare_cbor_raw_fuel expects
// option_nat_decrement_safe (NG.option_sz_v map_bound). We bridge those via the
// pure lemma option_sz_decrement_safe_v, invoked in the outer body so SMT can
// reconcile the closure type at the use site.

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

// NOTE: deliberately NOT `inline_for_extraction noextract` here, unlike
// Det.Compare's `impl_cbor_compare_fuel`. The Nondet body unfolds (via the
// `inline_for_extraction` helpers `compare_cbor_raw_fuel`,
// `compare_cbor_raw_list_for_all_fuel`, etc.) to ~6 call sites of the two
// inner closures `ih_rec` and `ih_rec_map`. If this recursive function were
// `inline_for_extraction`, each of those call sites would β-reduce to a
// fresh inlined copy of the entire body, then expand again — causing
// exponential blow-up during Pulse --codegen krml. Det.Compare gets away with
// `inline_for_extraction` because its body has only one inner closure `ih`,
// matching the OLD non-fuel `compare_cbor_raw_basic` which was likewise a
// top-level extracted recursive function.
```pulse
fn rec compare_cbor_raw_basic_fuel
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
  cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
  pure (raw_data_item_size v1 <= Ghost.reveal n /\
        raw_data_item_size v2 <= Ghost.reveal n)
returns res: option bool
ensures
  cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
  cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
  pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2)
decreases (Ghost.reveal n)
{
  cbor_raw_match_fuel_implies_pos (Ghost.reveal n) x1 #pm1 #v1;
  let m : Ghost.erased nat = Ghost.hide (Ghost.reveal n - 1);
  let mb_dec = option_sz_decrement_safe map_bound;
  option_sz_decrement_safe_v map_bound;

  // ih_rec: callback at fuel m, same map_bound. Type matches
  // compare_cbor_raw_fuel_t basic_data_model (NG.option_sz_v map_bound) m.
  fn ih_rec
    (y1: cbor_raw)
    (y2: cbor_raw)
    (#qm1: perm)
    (#w1: Ghost.erased raw_data_item)
    (#qm2: perm)
    (#w2: Ghost.erased raw_data_item)
  requires
    cbor_raw_match_fuel (Ghost.reveal m) qm1 y1 w1 **
    cbor_raw_match_fuel (Ghost.reveal m) qm2 y2 w2 **
    pure (raw_data_item_size w1 <= Ghost.reveal m /\
          raw_data_item_size w2 <= Ghost.reveal m)
  returns res2: option bool
  ensures
    cbor_raw_match_fuel (Ghost.reveal m) qm1 y1 w1 **
    cbor_raw_match_fuel (Ghost.reveal m) qm2 y2 w2 **
    pure (res2 == check_equiv basic_data_model (NG.option_sz_v map_bound) w1 w2)
  {
    compare_cbor_raw_basic_fuel f64 map_bound m y1 y2 #qm1 #w1 #qm2 #w2
  };

  // ih_rec_map: callback at fuel m, decremented map_bound. Its post talks about
  // NG.option_sz_v mb_dec; the lemma above lets SMT bridge this to
  // option_nat_decrement_safe (NG.option_sz_v map_bound), which is what
  // compare_cbor_raw_fuel's compare_rec_map parameter expects.
  fn ih_rec_map
    (y1: cbor_raw)
    (y2: cbor_raw)
    (#qm1: perm)
    (#w1: Ghost.erased raw_data_item)
    (#qm2: perm)
    (#w2: Ghost.erased raw_data_item)
  requires
    cbor_raw_match_fuel (Ghost.reveal m) qm1 y1 w1 **
    cbor_raw_match_fuel (Ghost.reveal m) qm2 y2 w2 **
    pure (raw_data_item_size w1 <= Ghost.reveal m /\
          raw_data_item_size w2 <= Ghost.reveal m)
  returns res2: option bool
  ensures
    cbor_raw_match_fuel (Ghost.reveal m) qm1 y1 w1 **
    cbor_raw_match_fuel (Ghost.reveal m) qm2 y2 w2 **
    pure (res2 == check_equiv basic_data_model (NG.option_sz_v mb_dec) w1 w2)
  {
    compare_cbor_raw_basic_fuel f64 mb_dec m y1 y2 #qm1 #w1 #qm2 #w2
  };

  // impl_dm_basic_fuel: fuel-aware data_model for basic_data_model, which is
  // the constant-false relation. Just returns false.
  fn impl_dm_basic_fuel
    (y1: cbor_raw)
    (y2: cbor_raw)
    (#qm1: perm)
    (#w1: Ghost.erased raw_data_item)
    (#qm2: perm)
    (#w2: Ghost.erased raw_data_item)
  requires
    cbor_raw_match_fuel (Ghost.reveal n) qm1 y1 w1 **
    cbor_raw_match_fuel (Ghost.reveal n) qm2 y2 w2
  returns res2: bool
  ensures
    cbor_raw_match_fuel (Ghost.reveal n) qm1 y1 w1 **
    cbor_raw_match_fuel (Ghost.reveal n) qm2 y2 w2 **
    pure (res2 == basic_data_model w1 w2)
  {
    false
  };

  compare_cbor_raw_fuel #basic_data_model n impl_dm_basic_fuel f64 map_bound
    ih_rec ih_rec_map x1 x2 #pm1 #v1 #pm2 #v2
}
```

#pop-options

// === Phase 7: non-fuel wrapper using cbor_raw_match_to_fuel ===
//
// Bridges cbor_raw_match back into the fuel-aware world by computing a fuel
// level n large enough to (a) re-establish cbor_raw_match_fuel for both inputs
// via cbor_raw_match_fuel_weaken, and (b) satisfy the size precondition of
// compare_cbor_raw_basic_fuel. We pick n as the max over both per-input fuels
// (from cbor_raw_match_to_fuel) and both input sizes (so the size precondition
// is discharged by the definition of nat_max).

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
fn compare_cbor_raw_basic
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2
returns res: option bool
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2)
{
  let n1 = cbor_raw_match_to_fuel x1 #pm1 #v1;
  let n2 = cbor_raw_match_to_fuel x2 #pm2 #v2;
  let n : Ghost.erased nat = Ghost.hide (
    nat_max
      (nat_max (Ghost.reveal n1) (Ghost.reveal n2))
      (nat_max (raw_data_item_size v1) (raw_data_item_size v2))
  );
  cbor_raw_match_fuel_weaken (Ghost.reveal n1) (Ghost.reveal n) x1 #pm1 #v1;
  cbor_raw_match_fuel_weaken (Ghost.reveal n2) (Ghost.reveal n) x2 #pm2 #v2;
  let res = compare_cbor_raw_basic_fuel f64 map_bound n x1 x2 #pm1 #v1 #pm2 #v2;
  cbor_raw_match_of_fuel (Ghost.reveal n) x1 #pm1 #v1;
  cbor_raw_match_of_fuel (Ghost.reveal n) x2 #pm2 #v2;
  res
}
```

#pop-options

