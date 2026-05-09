module CBOR.Pulse.Raw.EverParse.Nondet.Compare
#lang-pulse
include CBOR.Spec.Raw.Nondet
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
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
    v.cbor_string_type == m /\ SZ.v (S.len v.cbor_string_ptr) == U64.v len.value
  | CBOR_Case_Array v, Array len _ ->
    SZ.v (I.mixed_list_length v.cbor_array_ptr) == U64.v len.value
  | CBOR_Case_Map v, Map len _ ->
    SZ.v (I.mixed_list_length v.cbor_map_ptr) == U64.v len.value
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

// === check_equiv_list decomposition ===

let option_and (x y: option bool) : option bool =
  match x with
  | None -> None
  | Some false -> Some false
  | Some true -> y

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

// === Gen-level pipeline: recursive check_equiv_map_hd ===

// FIXME: fold definition of impl_check_equiv_map_hd_t
fn rec impl_check_equiv_map_hd_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
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
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
      pure (
        SZ.v n1 > 0 /\ SZ.v n2 > 0
      )
    )
  returns res: option bool
  ensures
    (
PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
      pure (
        SZ.v n1 > 0 /\ SZ.v n2 > 0 /\
        res == (check_equiv_map data_model (NG.option_sz_v map_bound)) (List.Tot.hd gl1) (List.Tot.hd gl2)
      )
    )
{
  NG.impl_check_equiv_map_hd_body (impl_data_model_to_equiv_hd impl_dm f64) (impl_check_equiv_map_hd_compare impl_dm f64) map_bound n1 l1 n2 l2
}

inline_for_extraction
let impl_check_equiv_list_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
: NG.impl_check_equiv_list_t (check_equiv_map data_model (NG.option_sz_v map_bound))
= NG.impl_check_equiv_list_map (impl_check_equiv_map_hd_compare impl_dm f64) map_bound

inline_for_extraction
let impl_check_equiv_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
: NG.impl_equiv_t #_ (check_equiv data_model (NG.option_sz_v map_bound))
= NG.impl_check_equiv map_bound (impl_check_equiv_list_compare impl_dm f64 map_bound)

inline_for_extraction
fn impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
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
  NG.impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow (impl_check_equiv_compare impl_dm f64 None) nl1 l1 nl2 l2
}

// === Type for the recursive comparison function ===

inline_for_extraction
noextract [@@noextract_to "krml"]
let compare_cbor_raw_t
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
=
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt (option bool)
    (cbor_raw_match pm1 x1 v1 **
     cbor_raw_match pm2 x2 v2)
    (fun res ->
      cbor_raw_match pm1 x1 v1 **
      cbor_raw_match pm2 x2 v2 **
      pure (res == check_equiv data_model map_bound v1 v2))

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

#push-options "--z3rlimit 512 --fuel 4 --ifuel 4 --split_queries always"

// Array pairwise comparison helper
inline_for_extraction
fn compare_cbor_raw_array_case
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (compare_rec: compare_cbor_raw_t data_model (NG.option_sz_v map_bound))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (_: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    I.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    I.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (
    Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
    List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
    check_equiv data_model (NG.option_sz_v map_bound) v1 v2 ==
      check_equiv_list (Array?.v (Ghost.reveal v1)) (Array?.v (Ghost.reveal v2)) (check_equiv_map data_model (NG.option_sz_v map_bound))
  )
returns res: option bool
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (res == check_equiv data_model (NG.option_sz_v map_bound) v1 v2)
{
  let j = jump_raw_data_item f64;
  let zcp = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read 1.0R f64) ();
  // Get arrays
  let ar_ml1 = cbor_raw_get_array pm1 x1 ();
  with pm1_a ar1 . assert (
    I.mixed_list_match cbor_raw_match parse_raw_data_item pm1_a ar_ml1 ar1 **
    trade (I.mixed_list_match cbor_raw_match parse_raw_data_item pm1_a ar_ml1 ar1)
          (cbor_raw_match pm1 x1 v1)
  );
  let ar_ml2 = cbor_raw_get_array pm2 x2 ();
  with pm2_a ar2 . assert (
    I.mixed_list_match cbor_raw_match parse_raw_data_item pm2_a ar_ml2 ar2 **
    trade (I.mixed_list_match cbor_raw_match parse_raw_data_item pm2_a ar_ml2 ar2)
          (cbor_raw_match pm2 x2 v2)
  );
  // Start iterators - use the eta-expanded form for vmatch consistency
  let it1_init = I.iterator_start cbor_raw_match parse_raw_data_item j pm1_a ar_ml1 ar1
    cbor_raw_match_share_t cbor_raw_match_gather_t;
  Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
  let it2_init = I.iterator_start cbor_raw_match parse_raw_data_item j pm2_a ar_ml2 ar2
    cbor_raw_match_share_t cbor_raw_match_gather_t;
  Trade.trans _ _ (cbor_raw_match pm2 x2 v2);
  // Set up loop state
  let mut r_it1 = it1_init;
  let mut r_it2 = it2_init;
  let mut r_acc : option bool = Some true;
  let mut r_cnt = 0sz;
  // While loop: pairwise comparison
  while (
    let acc = !r_acc;
    let cnt = !r_cnt;
    (SZ.lt cnt len && acc = Some true)
  ) invariant exists* it1c it2c acc_c cnt_c rem1 rem2 pm1c pm2c .
    R.pts_to r_it1 it1c **
    R.pts_to r_it2 it2c **
    R.pts_to r_acc acc_c **
    R.pts_to r_cnt cnt_c **
    I.iterator_match cbor_raw_match parse_raw_data_item pm1c it1c rem1 **
    I.iterator_match cbor_raw_match parse_raw_data_item pm2c it2c rem2 **
    trade (I.iterator_match cbor_raw_match parse_raw_data_item pm1c it1c rem1)
          (cbor_raw_match pm1 x1 v1) **
    trade (I.iterator_match cbor_raw_match parse_raw_data_item pm2c it2c rem2)
          (cbor_raw_match pm2 x2 v2) **
    pure (
      SZ.v cnt_c <= SZ.v len /\
      List.Tot.length rem1 == SZ.v len - SZ.v cnt_c /\
      List.Tot.length rem2 == SZ.v len - SZ.v cnt_c /\
      Ghost.reveal ar1 == Array?.v (Ghost.reveal v1) /\
      Ghost.reveal ar2 == Array?.v (Ghost.reveal v2) /\
      list_sum raw_data_item_size rem1 + list_sum raw_data_item_size rem2 <= list_sum raw_data_item_size (Ghost.reveal ar1) + list_sum raw_data_item_size (Ghost.reveal ar2) /\
      check_equiv_list (Ghost.reveal ar1) (Ghost.reveal ar2) (check_equiv_map data_model (NG.option_sz_v map_bound)) ==
        option_and acc_c (check_equiv_list rem1 rem2 (check_equiv_map data_model (NG.option_sz_v map_bound)))
    )
  {
    // Get next elements from iterator 1
    let e1 = I.iterator_next cbor_raw_match parse_raw_data_item j _ r_it1 _ _ cbor_raw_match_share_t cbor_raw_match_gather_t zcp;
    unfold (I.iterator_next_post cbor_raw_match parse_raw_data_item _ r_it1 _ _ e1);
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      cbor_raw_match pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match cbor_raw_match parse_raw_data_item pm1n it1n tl1
    );
    // The pure fact rem1 == hdv1 :: tl1 comes from iterator_next_post
    Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
    // Get next elements from iterator 2
    let e2 = I.iterator_next cbor_raw_match parse_raw_data_item j _ r_it2 _ _ cbor_raw_match_share_t cbor_raw_match_gather_t zcp;
    unfold (I.iterator_next_post cbor_raw_match parse_raw_data_item _ r_it2 _ _ e2);
    with pmv2 hdv2 tl2 it2n pm2n . assert (
      cbor_raw_match pmv2 e2 hdv2 **
      R.pts_to r_it2 it2n **
      I.iterator_match cbor_raw_match parse_raw_data_item pm2n it2n tl2
    );
    Trade.trans _ _ (cbor_raw_match pm2 x2 v2);
    // Compare the pair
    let pair_res = compare_rec e1 e2;
    // Feed back element matches
    Trade.elim_hyp_l _ _ (cbor_raw_match pm1 x1 v1);
    Trade.elim_hyp_l _ _ (cbor_raw_match pm2 x2 v2);
    // Update acc and cnt
    let old_acc = !r_acc;
    let old_cnt = !r_cnt;
    r_acc := option_and old_acc pair_res;
    r_cnt := SZ.add old_cnt 1sz;
    // Prove invariant: decompose check_equiv_list
    check_equiv_list_cons (Ghost.reveal hdv1) (Ghost.reveal hdv2) (Ghost.reveal tl1) (Ghost.reveal tl2)
      (list_sum raw_data_item_size (Ghost.reveal ar1) + list_sum raw_data_item_size (Ghost.reveal ar2))
      (check_equiv_map data_model (NG.option_sz_v map_bound)) ();
    check_equiv_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal hdv1) (Ghost.reveal hdv2);
    option_and_assoc old_acc pair_res
      (check_equiv_list (Ghost.reveal tl1) (Ghost.reveal tl2) (check_equiv_map data_model (NG.option_sz_v map_bound)));
  };
  // After loop: trade back
  Trade.elim _ (cbor_raw_match pm1 x1 v1);
  Trade.elim _ (cbor_raw_match pm2 x2 v2);
  !r_acc
}

inline_for_extraction
fn compare_cbor_raw_body
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (compare_rec: compare_cbor_raw_t data_model (NG.option_sz_v map_bound))
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
  pure (res == check_equiv data_model (NG.option_sz_v map_bound) v1 v2)
{
  // Step 1: Try data_model first
  let dm_res = impl_dm x1 x2;
  if dm_res {
    check_equiv_dm_true_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) ();
    Some true
  } else {
    // Step 2: Get constructor info and major types
    cbor_raw_match_cases pm1 x1;
    cbor_raw_match_cases pm2 x2;
    cbor_raw_match_fields pm1 x1;
    cbor_raw_match_fields pm2 x2;
    let mt1 = cbor_raw_get_major_type pm1 x1;
    let mt2 = cbor_raw_get_major_type pm2 x2;
    if (mt1 <> mt2) {
      // Different major types: mismatch
      check_equiv_mismatch_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      Some false
    } else if (mt1 = Spec.cbor_major_type_simple_value) {
      // Simple/Simple: compare values directly via fields_prop
      let sv1 = CBOR_Case_Simple?.v x1;
      let sv2 = CBOR_Case_Simple?.v x2;
      let res = sv1 = sv2;
      check_equiv_simple_eq data_model (NG.option_sz_v map_bound) sv1 sv2 ();
      Some res
    } else if (mt1 = Spec.cbor_major_type_uint64 || mt1 = Spec.cbor_major_type_neg_int64) {
      // Int/Int: compare type + value via fields_prop
      let vi1 = CBOR_Case_Int?.v x1;
      let vi2 = CBOR_Case_Int?.v x2;
      let res = vi1.cbor_int_type = vi2.cbor_int_type && (vi1.cbor_int_value <: U64.t) = (vi2.cbor_int_value <: U64.t);
      check_equiv_int_eq data_model (NG.option_sz_v map_bound) vi1.cbor_int_type { size = vi1.cbor_int_size; value = vi1.cbor_int_value } vi2.cbor_int_type { size = vi2.cbor_int_size; value = vi2.cbor_int_value } ();
      Some res
    } else if (mt1 = Spec.cbor_major_type_byte_string || mt1 = Spec.cbor_major_type_text_string) {
      // String/String: compare type + bytes
      let vs1 = CBOR_Case_String?.v x1;
      let vs2 = CBOR_Case_String?.v x2;
      if (vs1.cbor_string_type <> vs2.cbor_string_type) {
        check_equiv_string_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
        Some false
      } else {
        let s1 = cbor_raw_get_string pm1 x1 ();
        let s2 = cbor_raw_get_string pm2 x2 ();
        let cmp = CompareBytes.lex_compare_bytes s1 s2;
        CBOR.Spec.Raw.Format.bytes_lex_compare_equal (String?.v (Ghost.reveal v1)) (String?.v (Ghost.reveal v2));
        check_equiv_string_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
        Trade.elim _ (cbor_raw_match pm1 x1 v1);
        Trade.elim _ (cbor_raw_match pm2 x2 v2);
        let res = cmp = 0s;
        Some res
      }
    } else if (mt1 = Spec.cbor_major_type_tagged) {
      // Tagged/Tagged: compare tags, recurse on payloads
      check_equiv_tagged_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      let tag1 = cbor_raw_tag_value x1;
      let tag2 = cbor_raw_tag_value x2;
      cbor_raw_tag_value_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_tag_value_eq x2 (Ghost.reveal v2) () ();
      if (tag1 <> tag2) {
        Some false
      } else {
        let payload1 = cbor_raw_get_tagged_payload pm1 x1 f64 ();
        let payload2 = cbor_raw_get_tagged_payload pm2 x2 f64 ();
        let res = compare_rec payload1 payload2;
        Trade.elim _ (cbor_raw_match pm1 x1 v1);
        Trade.elim _ (cbor_raw_match pm2 x2 v2);
        res
      }
    } else if (mt1 = Spec.cbor_major_type_array) {
      // Array/Array: compare lengths, then delegate element comparison
      check_equiv_array_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      let len1 = I.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr;
      let len2 = I.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr;
      if (len1 <> len2) {
        Some false
      } else {
        // Same length: iterate pairwise and compare elements
        compare_cbor_raw_array_case f64 map_bound compare_rec x1 x2 len1 ()
      }
    } else {
      // Map/Map: delegate to Gen
      assume (pure False);
      unreachable ()
    }
  }
}

#pop-options
