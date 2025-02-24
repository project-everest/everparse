module CBOR.Pulse.API.Det.Common
#lang-pulse
include CBOR.Pulse.API.Det.Type
include CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives
module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module PM = Pulse.Lib.SeqMatch

val cbor_det_match: perm -> cbor_det_t -> Spec.cbor -> slprop

val cbor_det_match_with_size: nat -> perm -> cbor_det_t -> Spec.cbor -> slprop

val cbor_det_match_with_size_eq:
  (sz: nat) ->
  (p: perm) ->
  (c: cbor_det_t) ->
  (v: Spec.cbor) ->
  stt_ghost unit emp_inames
    (cbor_det_match_with_size sz p c v)
    (fun _ -> cbor_det_match_with_size sz p c v **
      pure (sz == Seq.length (Spec.cbor_det_serialize v))
    )

val cbor_det_reset_perm () : reset_perm_t cbor_det_match

val cbor_det_share () : share_t cbor_det_match
val cbor_det_gather () : gather_t cbor_det_match

(* SLProp-to-Prop abstraction vehicle to prove the correctness of type abstraction in the Rust API *)

[@@erasable]
noeq type cbor_det_case_t =
| CaseInt64
| CaseString
| CaseTagged
| CaseArray
| CaseMap
| CaseSimpleValue

val cbor_det_case: cbor_det_t -> cbor_det_case_t

noextract [@@noextract_to "krml"]
let cbor_det_case_correct_post
  (x: cbor_det_t)
  (v: Spec.cbor)
: Tot prop
= match cbor_det_case x, Spec.unpack v with
  | CaseInt64, Spec.CInt64 _ _
  | CaseString, Spec.CString _ _
  | CaseTagged, Spec.CTagged _ _
  | CaseArray, Spec.CArray _
  | CaseMap, Spec.CMap _
  | CaseSimpleValue, Spec.CSimple _
  -> True
  | _ -> False

val cbor_det_case_correct
  (x: cbor_det_t)
  (#p: perm)
  (#v: Spec.cbor)
: stt_ghost unit emp_inames
    (cbor_det_match p x v)
    (fun _ -> cbor_det_match p x v ** pure (cbor_det_case_correct_post x v))

(* Validation, parsing and serialization *)

noextract [@@noextract_to "krml"]
let cbor_det_validate_post
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
=
      if SZ.v res = 0
      then (~ (exists v1 v2 . v == Spec.cbor_det_serialize v1 `Seq.append` v2))
      else (exists v1 v2 . v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v res == Seq.length (Spec.cbor_det_serialize v1))

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_validate_t
=
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
val cbor_det_validate (_: unit) : cbor_det_validate_t

let cbor_det_parse_aux1
  (v1: Spec.cbor)
: Lemma
  (let s = Spec.cbor_det_serialize v1 in s == s `Seq.append` Seq.empty)
= Seq.append_empty_r (Spec.cbor_det_serialize v1)

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_parse_valid_t =
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_det_t
    (pts_to input #pm v ** pure (
      exists v1 . Ghost.reveal v == Spec.cbor_det_serialize v1 /\ SZ.v (S.len input) == Seq.length (Spec.cbor_det_serialize v1)
    ))
    (fun res -> exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade (cbor_det_match 1.0R res v') (pts_to input #pm v) ** pure (
        Ghost.reveal v == Spec.cbor_det_serialize v'
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
val cbor_det_parse_valid (_: unit) : cbor_det_parse_valid_t

let seq_length_append_l
  (#t: Type)
  (v1 v2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append v1 v2) 0 (Seq.length v1) == v1)
= assert (Seq.slice (Seq.append v1 v2) 0 (Seq.length v1) `Seq.equal` v1)

module SU = Pulse.Lib.Slice.Util

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_parse_full
  (cbor_det_validate: cbor_det_validate_t)
  (cbor_det_parse: cbor_det_parse_valid_t)
: cbor_det_parse_t u#0 #_ cbor_det_match
=
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  let len = cbor_det_validate input;
  Spec.cbor_det_parse_none_equiv v;
  if (len = 0sz) {
    fold (cbor_det_parse_post cbor_det_match input pm v None);
    None #(cbor_det_t & S.slice U8.t)
  } else {
    Seq.lemma_split v (SZ.v len);
    let input2, rem = SU.split_trade input len;
    Classical.forall_intro_2 (seq_length_append_l #U8.t);
    S.pts_to_len input2;
    let res = cbor_det_parse input2;
    Trade.trans_hyp_l _ _ _ (pts_to input #pm v);
    fold (cbor_det_parse_post_some cbor_det_match input pm v res rem);
    fold (cbor_det_parse_post cbor_det_match input pm v (Some (res, rem)));
    Some (res, rem)
  }
}

noextract [@@noextract_to "krml"]
let cbor_det_size_post
  (bound: SZ.t)
  (y: Spec.cbor)
  (res: SZ.t)
: Tot prop
=
      let s = Seq.length (Spec.cbor_det_serialize y) in
      (SZ.v res == 0 <==> s > SZ.v bound) /\
      (SZ.v res > 0 ==> SZ.v res == s)

val cbor_det_size
  (x: cbor_det_t)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt SZ.t
    (cbor_det_match pm x y)
    (fun res -> cbor_det_match pm x y ** pure (
      cbor_det_size_post bound y res
    ))

noextract [@@noextract_to "krml"]
let cbor_det_serialize_postcond
  (y: Spec.cbor)
  (res: SZ.t)
  (v: Seq.seq U8.t)
: Tot prop
=
      let s = Spec.cbor_det_serialize y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))

inline_for_extraction
noextract [@@noextract_to "krml"]
val cbor_det_serialize
  (x: cbor_det_t)
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt SZ.t
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (Seq.length (Spec.cbor_det_serialize y) <= SZ.v (S.len output)))
    (fun res -> exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      cbor_det_serialize_postcond y res v
    ))

noextract [@@noextract_to "krml"]
let cbor_det_serialize_tag_postcond
  (tag: U64.t)
  (output: S.slice U8.t)
  (res: SZ.t)
  (v': Seq.seq U8.t)
: Tot prop
= let s = Spec.cbor_det_serialize_tag tag in
  let len = Seq.length s in
  SZ.v (S.len output) == Seq.length v' /\
  (res == 0sz <==> len > Seq.length v') /\
  (len <= Seq.length v' ==> Seq.slice v' 0 len == s)

inline_for_extraction
noextract [@@noextract_to "krml"]
val cbor_det_serialize_tag
  (tag: U64.t)
  (output: S.slice U8.t)
: stt SZ.t
    (exists* v . pts_to output v)
    (fun res -> exists* v . pts_to output v ** pure (
      cbor_det_serialize_tag_postcond tag output res v
    ))

(* Constructors *)

val cbor_det_mk_simple_value () : mk_simple_t cbor_det_match
val cbor_det_mk_int64 () : mk_int64_t cbor_det_match
inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_det_mk_string () : mk_string_t cbor_det_match
val cbor_det_mk_tagged () : mk_tagged_t cbor_det_match
inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_det_mk_array () : mk_array_t cbor_det_match

val cbor_det_map_entry_match: perm -> cbor_det_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_det_mk_map_entry () : mk_map_entry_t cbor_det_match cbor_det_map_entry_match

inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_det_mk_map_gen () : mk_map_gen_by_ref_t cbor_det_match cbor_det_map_entry_match

(* Destructors *)

val cbor_det_equal () : equal_t cbor_det_match
val cbor_det_major_type () : get_major_type_t cbor_det_match
val cbor_det_read_simple_value () : read_simple_value_t cbor_det_match
val cbor_det_elim_simple () : elim_simple_t cbor_det_match
val cbor_det_read_uint64 () : read_uint64_t cbor_det_match
val cbor_det_elim_int64 () : elim_int64_t cbor_det_match
val cbor_det_get_string_length () : get_string_length_t cbor_det_match
inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_det_get_string () : get_string_t cbor_det_match
val cbor_det_get_tagged_tag () : get_tagged_tag_t cbor_det_match
val cbor_det_get_tagged_payload () : get_tagged_payload_t cbor_det_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_int64' = mk_int64_trade _ (cbor_det_mk_int64 ()) (cbor_det_elim_int64 ())

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_simple_value' = mk_simple_value_trade _ (cbor_det_mk_simple_value ()) (cbor_det_elim_simple ())

val cbor_det_get_array_length () : get_array_length_t cbor_det_match

val cbor_det_array_iterator_match : perm -> cbor_det_array_iterator_t -> list Spec.cbor -> slprop

val cbor_det_array_iterator_start () : array_iterator_start_t cbor_det_match cbor_det_array_iterator_match

val cbor_det_array_iterator_is_empty () : array_iterator_is_empty_t cbor_det_array_iterator_match

val cbor_det_array_iterator_length () : array_iterator_length_t cbor_det_array_iterator_match

val cbor_det_array_iterator_next () : array_iterator_next_t cbor_det_match cbor_det_array_iterator_match

val cbor_det_array_iterator_truncate () : array_iterator_truncate_t cbor_det_array_iterator_match

val cbor_det_array_iterator_share () : share_t cbor_det_array_iterator_match

val cbor_det_array_iterator_gather () : gather_t cbor_det_array_iterator_match

val cbor_det_get_array_item () : get_array_item_t cbor_det_match

val cbor_det_get_map_length () : get_map_length_t cbor_det_match

val cbor_det_map_iterator_match : perm -> cbor_det_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_det_map_iterator_start () : map_iterator_start_t cbor_det_match cbor_det_map_iterator_match

val cbor_det_map_iterator_is_empty () : map_iterator_is_empty_t cbor_det_map_iterator_match

val cbor_det_map_iterator_next () : map_iterator_next_t cbor_det_map_entry_match cbor_det_map_iterator_match

val cbor_det_map_iterator_share () : share_t cbor_det_map_iterator_match

val cbor_det_map_iterator_gather () : gather_t cbor_det_map_iterator_match

val cbor_det_map_entry_key () : map_entry_key_t cbor_det_map_entry_match cbor_det_match

val cbor_det_map_entry_value () : map_entry_value_t cbor_det_map_entry_match cbor_det_match

val cbor_det_map_entry_share () : share_t cbor_det_map_entry_match

val cbor_det_map_entry_gather () : gather_t cbor_det_map_entry_match

inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_det_map_get () : map_get_by_ref_t cbor_det_match
