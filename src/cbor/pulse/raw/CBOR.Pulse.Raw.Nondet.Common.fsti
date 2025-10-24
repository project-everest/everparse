module CBOR.Pulse.Raw.Nondet.Common
open CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives

module Spec = CBOR.Spec.API.Format
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module SM = Pulse.Lib.SeqMatch.Util

val cbor_nondet_t: Type0

val cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop

inline_for_extraction noextract [@@noextract_to "krml"]
val cbor_nondet_reset_perm
  (p: perm)
  (c: cbor_nondet_t)
  (r: Ghost.erased Spec.cbor)
  (q: perm)
: stt cbor_nondet_t
  (requires
    cbor_nondet_match p c r
  )
  (ensures fun c' ->
    cbor_nondet_match q c' r **
    Trade.trade
      (cbor_nondet_match q c' r)
      (cbor_nondet_match p c r)
  )

val cbor_nondet_share
  (_: unit)
: CBOR.Pulse.API.Base.share_t u#0 u#0 #_ #_ cbor_nondet_match

val cbor_nondet_gather
  (_: unit)
: CBOR.Pulse.API.Base.gather_t u#0 u#0 #_ #_ cbor_nondet_match

noextract [@@noextract_to "krml"]
let cbor_nondet_validate_post
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
=
  let r = Spec.cbor_parse v in
  if SZ.v res = 0
  then (Some? r ==> (Some? map_key_bound /\ Spec.cbor_map_key_depth (fst (Some?.v r)) > SZ.v (Some?.v map_key_bound)))
  else (
    Some? r /\
    SZ.v res == snd (Some?.v r) /\
    ((Some? map_key_bound /\ strict_check) ==> Spec.cbor_map_key_depth (fst (Some?.v r)) <= SZ.v (Some?.v map_key_bound))
  )

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_validate_t
=
  (map_key_bound: option SZ.t) ->
  (strict_check: bool) ->
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_nondet_validate_post map_key_bound strict_check v res
    ))

val cbor_nondet_validate (_: unit) : cbor_nondet_validate_t

noextract [@@noextract_to "krml"]
let cbor_nondet_parse_valid_post
  (v: Seq.seq U8.t)
  (v': Spec.cbor)
: Tot prop
= let w = Spec.cbor_parse v in
  Some? w /\
  v' == fst (Some?.v w)

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_nondet_parse_valid_t
  (#cbor_nondet_t: Type)
  (cbor_nondet_match: perm -> cbor_nondet_t -> Spec.cbor -> slprop)
=
  (input: S.slice U8.t) ->
  (len: SZ.t) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_nondet_t
    (pts_to input #pm v ** pure (
      cbor_nondet_validate_post None false v len /\
      SZ.v len > 0
    ))
    (fun res -> exists* p' v' .
      cbor_nondet_match p' res v' **
      Trade.trade (cbor_nondet_match p' res v') (pts_to input #pm v) ** pure (
        cbor_nondet_parse_valid_post v v'
    ))

val cbor_nondet_parse_valid (_: unit) : cbor_nondet_parse_valid_t #cbor_nondet_t cbor_nondet_match

noextract [@@noextract_to "krml"]
let cbor_nondet_serialize_postcond
  (y: Spec.cbor)
  (v: Seq.seq U8.t)
  (v': Seq.seq U8.t)
  (res: option SZ.t)
: Tot prop
= match res with
  | None -> True // TODO: specify maximum length
  | Some len ->
    SZ.v len <= Seq.length v' /\
    Seq.length v' == Seq.length v /\
    Seq.equal (Seq.slice v' (SZ.v len) (Seq.length v)) (Seq.slice v (SZ.v len) (Seq.length v)) /\
    Spec.cbor_parse v' == Some (y, SZ.v len)

noextract [@@noextract_to "krml"]
let cbor_nondet_serialize_postcond_c
  (y: Spec.cbor)
  (v: Seq.seq U8.t)
  (v': Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= cbor_nondet_serialize_postcond y v v' (if res = 0sz then None else Some res)

inline_for_extraction
let cbor_nondet_serialize_t
  (#cbordet: Type)
  (cbor_det_match: perm -> cbordet -> Spec.cbor -> slprop)
=
  (x: cbordet) ->
  (output: S.slice U8.t) ->
  (#y: Ghost.erased Spec.cbor) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt (option SZ.t)
    (cbor_det_match pm x y ** pts_to output v)
    (fun res -> exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      cbor_nondet_serialize_postcond y v v' res
    ))

val cbor_nondet_serialize
  (_: unit)
: cbor_nondet_serialize_t #cbor_nondet_t cbor_nondet_match

(* Destructors *)

val cbor_nondet_major_type (_: unit) : get_major_type_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_simple_value (_: unit) : read_simple_value_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_simple (_: unit) : elim_simple_t u#0 #_ cbor_nondet_match

val cbor_nondet_read_uint64 (_: unit) : read_uint64_t u#0 #_ cbor_nondet_match

val cbor_nondet_elim_int64 (_: unit) : elim_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_string_length (_: unit) : get_string_length_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_string (_: unit) : get_string_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_tagged_tag (_: unit) : get_tagged_tag_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_tagged_payload (_: unit) : get_tagged_payload_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_array_length (_: unit) : get_array_length_t u#0 #_ cbor_nondet_match

val cbor_nondet_array_iterator_t: Type0

val cbor_nondet_array_iterator_match: perm -> cbor_nondet_array_iterator_t -> list Spec.cbor -> slprop

val cbor_nondet_array_iterator_start (_: unit) : array_iterator_start_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_is_empty (_: unit) : array_iterator_is_empty_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_length (_: unit) : array_iterator_length_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_next (_: unit) : array_iterator_next_t u#0 #_ #_ cbor_nondet_match cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_truncate (_: unit) : array_iterator_truncate_t u#0 #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_array_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_array_iterator_match

val cbor_nondet_get_array_item (_: unit) : get_array_item_t u#0 #_ cbor_nondet_match

val cbor_nondet_get_map_length (_: unit) : get_map_length_t u#0 #_ cbor_nondet_match

val cbor_nondet_map_iterator_t: Type0

val cbor_nondet_map_iterator_match: perm -> cbor_nondet_map_iterator_t -> list (Spec.cbor & Spec.cbor) -> slprop

val cbor_nondet_map_iterator_start (_: unit) : map_iterator_start_t u#0 u#0 #_ #_ cbor_nondet_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_is_empty (_: unit) : map_iterator_is_empty_t u#0 #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_t: Type0

val cbor_nondet_map_entry_match: perm -> cbor_nondet_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_nondet_map_iterator_next (_: unit) : map_iterator_next_t u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_share (_: unit) : share_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_iterator_gather (_: unit) : gather_t u#0 u#0 #_ #_ cbor_nondet_map_iterator_match

val cbor_nondet_map_entry_key (_: unit) : map_entry_key_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_value (_: unit) : map_entry_value_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match cbor_nondet_match

val cbor_nondet_map_entry_share
  (_: unit)
: share_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match

val cbor_nondet_map_entry_gather
  (_: unit)
: gather_t u#0 u#0 #_ #_ cbor_nondet_map_entry_match

(* Equality *)

val cbor_nondet_equal
  (x1: cbor_nondet_t)
  (#p1: perm)
  (#v1: Ghost.erased Spec.cbor)
  (x2: cbor_nondet_t)
  (#p2: perm)
  (#v2: Ghost.erased Spec.cbor)
: stt bool
(requires
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2
)
(ensures fun res ->
  cbor_nondet_match p1 x1 v1 **
  cbor_nondet_match p2 x2 v2 **
  pure (res == true <==> Ghost.reveal v1 == Ghost.reveal v2)
)

val cbor_nondet_map_get (_: unit)
: map_get_by_ref_t #_ cbor_nondet_match

(* Constructors *)

val cbor_nondet_mk_simple_value (_: unit) : mk_simple_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_int64 (_: unit) : mk_int64_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_string (_: unit) : mk_string_t u#0 #_ cbor_nondet_match

val cbor_nondet_mk_tagged (_: unit) : mk_tagged_t #_ cbor_nondet_match

val cbor_nondet_mk_array (_: unit) : mk_array_t #_ cbor_nondet_match

val cbor_nondet_mk_map_gen (_: unit)
: mk_map_gen_by_ref_t #cbor_nondet_t #cbor_nondet_map_entry_t cbor_nondet_match cbor_nondet_map_entry_match
