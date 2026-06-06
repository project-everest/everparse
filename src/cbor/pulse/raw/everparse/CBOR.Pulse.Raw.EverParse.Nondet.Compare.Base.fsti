module CBOR.Pulse.Raw.EverParse.Nondet.Compare.Base
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
module VCList = LowParse.Spec.VCList

// === Pure field correspondence between cbor_raw struct fields and raw_data_item ===

// Stronger version of cbor_raw_match_cases_prop that includes value-level facts
let cbor_raw_match_fields_prop (x: cbor_raw) (y: raw_data_item) : prop =
  match x, y with
  | CBOR_Case_Int v, Int64 m rv ->
    v.cbor_int_type == m /\ v.cbor_int_value == rv.value /\ v.cbor_int_size == rv.size
  | CBOR_Case_Simple sv, Simple sv' -> sv == sv'
  | CBOR_Case_String v, String m len _ ->
    v.cbor_string_type == m /\ v.cbor_string_size == len.size /\ SZ.v (S.len (to_slice v.cbor_string_ptr)) == U64.v len.value
  | CBOR_Case_Array v, Array len _ ->
    v.cbor_array_length_size == len.size /\ SZ.v (IT.mixed_list_length v.cbor_array_ptr) == U64.v len.value
  | CBOR_Case_Map v, Map len _ ->
    v.cbor_map_length_size == len.size /\ SZ.v (IT.mixed_list_length v.cbor_map_ptr) == U64.v len.value
  | CBOR_Case_Tagged v, Tagged tag _ -> v.cbor_tagged_tag == tag
  | CBOR_Case_Tagged_Serialized v, Tagged tag _ -> v.cbor_tagged_serialized_tag == tag
  | _, _ -> False

#push-options "--z3rlimit 512 --fuel 2 --ifuel 2"

val cbor_raw_match_fields_prop_of_header
  (x: cbor_raw)
  (y: raw_data_item)
  (h: header)
  (_: squash (cbor_raw_get_header x == Some h))
  (_: squash (dfst (synth_raw_data_item_recip y) == h))
: Lemma (cbor_raw_match_fields_prop x y)

#pop-options

// Helper ghost fn: derive cbor_raw_match_fields_prop from cbor_raw_match
val cbor_raw_match_fields
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
: stt_ghost unit emp_inames
    (cbor_raw_match pm x y)
    (fun _ -> cbor_raw_match pm x y ** pure (cbor_raw_match_fields_prop x y))

// Helper ghost fn: from cbor_raw_match_aux, derive the field correspondence.
val cbor_raw_match_aux_fields
  (r: perm -> cbor_raw -> raw_data_item -> slprop)
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
: stt_ghost unit emp_inames
    (cbor_raw_match_aux parse_raw_data_item r pm x y)
    (fun _ -> cbor_raw_match_aux parse_raw_data_item r pm x y ** pure (cbor_raw_match_fields_prop x y))

// === check_equiv_list decomposition ===

inline_for_extraction
let option_and (x y: option bool) : option bool =
  match x with
  | None -> None
  | Some b -> if b then y else Some false

let option_and_assoc (x y z: option bool)
: Lemma (option_and x (option_and y z) == option_and (option_and x y) z)
= ()

// check_equiv_list_weaken: subtyping coercion
let check_equiv_list_weaken
  (l1 l2: list raw_data_item)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
  (_: squash (list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 <= bound))
: Tot (r: option bool { r == check_equiv_list l1 l2 equiv })
= check_equiv_list l1 l2 equiv

val check_equiv_list_decompose
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
inline_for_extraction
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

// Per-case lemmas for check_equiv reduction on non-Map cases

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

// === Total wrappers (for post-condition use in case helpers) ===

let check_equiv_tagged_total
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (v1 v2: raw_data_item)
: Tot (option bool)
= match v1, v2 with
  | Tagged tag1 p1, Tagged tag2 p2 ->
    if tag1.value = tag2.value
    then check_equiv dm mb p1 p2
    else Some false
  | _ -> Some false

let check_equiv_array_total
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (v1 v2: raw_data_item)
: Tot (option bool)
= match v1, v2 with
  | Array _ _, Array _ _ -> check_equiv dm mb v1 v2
  | _ -> Some false

let check_equiv_map_total
  (dm: (raw_data_item -> raw_data_item -> bool))
  (mb: option nat)
  (v1 v2: raw_data_item)
: Tot (option bool)
= match v1, v2 with
  | Map _ _, Map _ _ -> check_equiv dm mb v1 v2
  | _ -> Some false

// Callback type: data_model implementation at the cbor_raw level.
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
val impl_data_model_to_equiv_hd
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
: NG.impl_equiv_hd_t data_model

// === Local instance of impl_data_model_t for basic_data_model ===
inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_nondet_impl_basic_local
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: stt bool
    (cbor_raw_match pm1 x1 v1 **
     cbor_raw_match pm2 x2 v2)
    (fun res ->
      cbor_raw_match pm1 x1 v1 **
      cbor_raw_match pm2 x2 v2 **
      pure (res == basic_data_model v1 v2))

// === Gen-level pipeline: non-recursive check_equiv_map_hd ===

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
val impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_compare
  (#data_model: Ghost.erased ((x1: raw_data_item) -> (x2: raw_data_item) -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
  (ih: NG.impl_check_equiv_map_hd_t data_model)
  (nl1: SZ.t)
  (l1: S.slice byte)
  (nl2: SZ.t)
  (l2: S.slice byte)
  (#pl1: perm)
  (#gl1: Ghost.erased (VCList.nlist (SZ.v nl1) (raw_data_item & raw_data_item)))
  (#pl2: perm)
  (#gl2: Ghost.erased (VCList.nlist (SZ.v nl2) (raw_data_item & raw_data_item)))
: stt (option bool)
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl1) (nondep_then parse_raw_data_item parse_raw_data_item)) l1 #pl1 gl1 **
     PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl2) (nondep_then parse_raw_data_item parse_raw_data_item)) l2 #pl2 gl2)
    (fun res ->
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl1) (nondep_then parse_raw_data_item parse_raw_data_item)) l1 #pl1 gl1 **
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v nl2) (nondep_then parse_raw_data_item parse_raw_data_item)) l2 #pl2 gl2 **
      pure (
        res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow (check_equiv data_model None) (check_equiv data_model None) gl1) gl2
      ))

// === Specialized recursive instance: check_equiv_map_hd for basic_data_model ===

val impl_check_equiv_map_hd_basic
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (VCList.nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (VCList.nlist (SZ.v n2) raw_data_item))
: stt (option bool)
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
     PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
     pure (
       SZ.v n1 > 0 /\ SZ.v n2 > 0
     ))
    (fun res ->
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1 **
      PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2 **
      pure (
        SZ.v n1 > 0 /\ SZ.v n2 > 0 /\
        res == (check_equiv_map basic_data_model (NG.option_sz_v map_bound)) (List.Tot.hd gl1) (List.Tot.hd gl2)
      ))

// === Type for the recursive comparison function ===

// Fuel-aware variant of compare_cbor_raw_t.
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

val setoid_assoc_eq_with_overflow_check_equiv_ext
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

val list_for_all_with_overflow_ext
  (#t: Type)
  (f g: t -> option bool)
  (l: list t)
: Lemma
  (requires forall x . List.Tot.memP x l ==> f x == g x)
  (ensures list_for_all_with_overflow f l == list_for_all_with_overflow g l)
  (decreases l)

val check_equiv_map_list_for_all_ext
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

// === Body of the recursive comparison function: helpers ===

// Coerce Pulse ghost fn to stt_ghost for share_t / gather_t
val cbor_raw_match_share_wrapper
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item)
: stt_ghost unit emp_inames
    (cbor_raw_match p x1 x2)
    (fun _ -> cbor_raw_match (p /. 2.0R) x1 x2 ** cbor_raw_match (p /. 2.0R) x1 x2)

val cbor_raw_match_gather_wrapper
  (x1: cbor_raw) (#p: perm) (#x2: raw_data_item) (#p': perm) (#x2': raw_data_item)
: stt_ghost unit emp_inames
    (cbor_raw_match p x1 x2 ** cbor_raw_match p' x1 x2')
    (fun _ -> cbor_raw_match (p +. p') x1 x2 ** pure (x2 == x2'))

let cbor_raw_match_share_t : I.share_t cbor_raw_match = cbor_raw_match_share_wrapper
let cbor_raw_match_gather_t : I.gather_t cbor_raw_match = cbor_raw_match_gather_wrapper

// Map entry vmatch: the vmatch used for map entries in mixed_list_match
let cbor_map_entry_vmatch
  (pm: perm)
  (elem: cbor_map_entry cbor_raw)
  (v: (raw_data_item & raw_data_item))
: Tot slprop
= cbor_map_entry_match cbor_raw_match pm elem v

val cbor_map_entry_vmatch_share_wrapper
  (entry: cbor_map_entry cbor_raw) (#pm: perm) (#pair: (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_map_entry_vmatch pm entry pair)
    (fun _ -> cbor_map_entry_vmatch (pm /. 2.0R) entry pair ** cbor_map_entry_vmatch (pm /. 2.0R) entry pair)

val cbor_map_entry_vmatch_gather_wrapper
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm) (#pair: (raw_data_item & raw_data_item))
  (#pm': perm) (#pair': (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_map_entry_vmatch pm entry pair ** cbor_map_entry_vmatch pm' entry pair')
    (fun _ -> cbor_map_entry_vmatch (pm +. pm') entry pair ** pure (pair == pair'))

let cbor_map_entry_vmatch_share : I.share_t cbor_map_entry_vmatch = cbor_map_entry_vmatch_share_wrapper
let cbor_map_entry_vmatch_gather : I.gather_t cbor_map_entry_vmatch = cbor_map_entry_vmatch_gather_wrapper

// zero_copy_parse for map entries
inline_for_extraction
val cbor_map_entry_zero_copy_parse
  (f64: squash SZ.fits_u64)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
: stt (cbor_map_entry cbor_raw)
    (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
    (fun res ->
      cbor_map_entry_vmatch 1.0R res v **
      Trade.trade (cbor_map_entry_vmatch 1.0R res v)
                  (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v))

// Unfold cbor_map_entry_vmatch to expose key and value cbor_raw_match
val unfold_map_entry_vmatch
  (pm: perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_map_entry_vmatch pm entry pair)
    (fun _ ->
      cbor_raw_match pm entry.cbor_map_entry_key (fst pair) **
      cbor_raw_match pm entry.cbor_map_entry_value (snd pair))

// Fold cbor_raw_match for key and value back into cbor_map_entry_vmatch
val fold_map_entry_vmatch
  (pm: perm)
  (entry: cbor_map_entry cbor_raw)
  (pair: (raw_data_item & raw_data_item))
: stt_ghost unit emp_inames
    (cbor_raw_match pm entry.cbor_map_entry_key (fst pair) **
     cbor_raw_match pm entry.cbor_map_entry_value (snd pair))
    (fun _ -> cbor_map_entry_vmatch pm entry pair)

// Fuel-aware variant of compare_cbor_raw_fn_t.
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

// Fuel-aware variant of impl_data_model_t.
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

// === Local type abbreviations for the three callbacks ===

inline_for_extraction noextract [@@noextract_to "krml"]
let compare_cbor_raw_basic_fuel_tagged_local_t
  (n: Ghost.erased nat)
  (map_bound: option SZ.t)
=
  (n_pos: squash (Ghost.reveal n >= 1)) ->
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt (option bool)
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (Tagged? (Ghost.reveal v1) /\ Tagged? (Ghost.reveal v2) /\
           raw_data_item_size (Ghost.reveal v1) <= Ghost.reveal n /\
           raw_data_item_size (Ghost.reveal v2) <= Ghost.reveal n))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (res == check_equiv_tagged_total basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2)))

inline_for_extraction noextract [@@noextract_to "krml"]
let compare_cbor_raw_basic_fuel_array_local_t
  (n: Ghost.erased nat)
  (map_bound: option SZ.t)
=
  (n_pos: squash (Ghost.reveal n >= 1)) ->
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (len: SZ.t) ->
  (sq: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  )) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt (option bool)
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (
       Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
       List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
       List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
       raw_data_item_size (Ghost.reveal v1) <= Ghost.reveal n /\
       raw_data_item_size (Ghost.reveal v2) <= Ghost.reveal n
     ))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (res == check_equiv_array_total basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2)))

inline_for_extraction noextract [@@noextract_to "krml"]
let compare_cbor_raw_basic_fuel_map_local_t
  (n: Ghost.erased nat)
  (map_bound: option SZ.t)
=
  (n_pos: squash (Ghost.reveal n >= 1)) ->
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt (option bool)
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (Map? (Ghost.reveal v1) /\ Map? (Ghost.reveal v2) /\
           raw_data_item_size (Ghost.reveal v1) <= Ghost.reveal n /\
           raw_data_item_size (Ghost.reveal v2) <= Ghost.reveal n))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (res == check_equiv_map_total basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2)))
