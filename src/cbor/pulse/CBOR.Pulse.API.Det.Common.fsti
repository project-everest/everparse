module CBOR.Pulse.API.Det.Common
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

val cbor_det_validate
  (input: S.slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))

val cbor_det_parse
  (input: S.slice U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt cbor_det_t
    (pts_to input #pm v ** pure (
      exists v1 v2 . Ghost.reveal v == Spec.cbor_det_serialize v1 `Seq.append` v2 /\ SZ.v len == Seq.length (Spec.cbor_det_serialize v1)
    ))
    (fun res -> exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade (cbor_det_match 1.0R res v') (pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == Spec.cbor_det_serialize v'
    ))

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

val cbor_det_serialize
  (x: cbor_det_t)
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt SZ.t
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (Seq.length (Spec.cbor_det_serialize y) <= SZ.v (S.len output)))
    (fun res -> exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      let s = Spec.cbor_det_serialize y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    ))

(* Constructors *)

val cbor_det_mk_simple_value () : mk_simple_t cbor_det_match
val cbor_det_mk_int64 () : mk_int64_t cbor_det_match
val cbor_det_mk_string () : mk_string_t cbor_det_match
val cbor_det_mk_tagged () : mk_tagged_t cbor_det_match
val cbor_det_mk_array () : mk_array_t cbor_det_match

val cbor_det_map_entry_match: perm -> cbor_det_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_det_mk_map_entry () : mk_map_entry_t cbor_det_match cbor_det_map_entry_match

val cbor_det_mk_map_gen () : mk_map_gen_t cbor_det_match cbor_det_map_entry_match

inline_for_extraction [@@noextract_to "krml"]
let cbor_det_mk_map () : mk_map_t cbor_det_match cbor_det_map_entry_match =
  mk_map (cbor_det_mk_map_gen ())

(* Destructors *)

val cbor_det_equal () : equal_t cbor_det_match
val cbor_det_major_type () : get_major_type_t cbor_det_match
val cbor_det_read_simple_value () : read_simple_value_t cbor_det_match
val cbor_det_read_uint64 () : read_uint64_t cbor_det_match
val cbor_det_get_string () : get_string_t cbor_det_match
val cbor_det_get_tagged_tag () : get_tagged_tag_t cbor_det_match
val cbor_det_get_tagged_payload () : get_tagged_payload_t cbor_det_match

val cbor_det_get_array_length () : get_array_length_t cbor_det_match

val cbor_det_array_iterator_match : perm -> cbor_det_array_iterator_t -> list Spec.cbor -> slprop

val cbor_det_array_iterator_start () : array_iterator_start_t cbor_det_match cbor_det_array_iterator_match

val cbor_det_array_iterator_is_empty () : array_iterator_is_empty_t cbor_det_array_iterator_match

val cbor_det_array_iterator_next () : array_iterator_next_t cbor_det_match cbor_det_array_iterator_match

val cbor_det_get_array_item () : get_array_item_t cbor_det_match

val cbor_det_get_map_length () : get_map_length_t cbor_det_match

val cbor_det_map_iterator_match : perm -> cbor_det_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_det_map_iterator_start () : map_iterator_start_t cbor_det_match cbor_det_map_iterator_match

val cbor_det_map_iterator_is_empty () : map_iterator_is_empty_t cbor_det_map_iterator_match

val cbor_det_map_iterator_next () : map_iterator_next_t cbor_det_map_entry_match cbor_det_map_iterator_match

val cbor_det_map_entry_key () : map_entry_key_t cbor_det_map_entry_match cbor_det_match

val cbor_det_map_entry_value () : map_entry_value_t cbor_det_map_entry_match cbor_det_match

val cbor_det_map_get () : map_get_t cbor_det_match
