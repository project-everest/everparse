module CBOR.Pulse.API.Det.C
#lang-pulse
include CBOR.Pulse.API.Det.Type
include CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives
open CBOR.Spec.Constants

module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8

module SU = Pulse.Lib.Slice.Util
module AP = Pulse.Lib.ArrayPtr

val cbor_det_match: perm -> cbor_det_t -> Spec.cbor -> slprop

val cbor_det_reset_perm () : reset_perm_t cbor_det_match

val cbor_det_share () : share_t cbor_det_match
val cbor_det_gather () : gather_t cbor_det_match

val cbor_det_validate
  (input: AP.ptr U8.t)
  (input_len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (pts_to input #pm v ** pure (SZ.v input_len == Seq.length v))
    (fun res -> pts_to input #pm v ** pure (
      cbor_det_validate_post v res
    ))

val cbor_det_parse
  (input: AP.ptr U8.t)
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
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt SZ.t
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
    (fun res -> exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      SZ.v output_len == Seq.length v /\
      cbor_det_serialize_fits_postcond y res v
    ))

val cbor_det_serialize_safe
  (x: cbor_det_t)
  (output: AP.ptr U8.t)
  (output_len: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#pm: perm)
: stt SZ.t
    (cbor_det_match pm x y ** pts_to output v ** pure (SZ.v output_len == Seq.length v /\ Seq.length (Spec.cbor_det_serialize y) <= SZ.v output_len))
    (fun res -> exists* v' . cbor_det_match pm x y ** pts_to output v' ** pure (
      SZ.v output_len == Seq.length v' /\
      cbor_det_serialize_postcond_c y v v' res
    ))

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_serialize_to_slice
  (x: cbor_det_t)
  (output: S.slice U8.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
requires
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (Seq.length (Spec.cbor_det_serialize y) <= SZ.v (S.len output)))
returns res: SZ.t
ensures
    (exists* v . cbor_det_match pm x y ** pts_to output v ** pure (
      cbor_det_serialize_fits_postcond y res v
    ))
{
  S.pts_to_len output;
  let len = S.len output;
  let ou = S.slice_to_arrayptr_intro output;
  let res = cbor_det_serialize x ou len;
  S.slice_to_arrayptr_elim ou;
  res
}

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_impl_utf8_correct_from_array_t =
  (s: AP.ptr U8.t) ->
  (len: SZ.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt bool
    (pts_to s #p v ** pure (SZ.v len == Seq.length v))
    (fun res -> pts_to s #p v ** pure (res == CBOR.Spec.API.UTF8.correct v))

val cbor_det_impl_utf8_correct_from_array (_: unit) : cbor_det_impl_utf8_correct_from_array_t

(* Constructors *)

val cbor_det_mk_simple_value () : mk_simple_t cbor_det_match
val cbor_det_mk_int64 () : mk_int64_t cbor_det_match
val cbor_det_mk_tagged () : mk_tagged_t cbor_det_match

val cbor_det_mk_string_from_arrayptr (_: unit) : mk_string_from_arrayptr_t cbor_det_match

val cbor_det_mk_array_from_array (_: unit) : mk_array_from_array_t cbor_det_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_array_from_array' = mk_array_from_array' (cbor_det_mk_array_from_array ())

val cbor_det_map_entry_match: perm -> cbor_det_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_det_mk_map_entry () : mk_map_entry_t cbor_det_match cbor_det_map_entry_match

val cbor_det_mk_map_from_array : mk_map_from_array_t cbor_det_match cbor_det_map_entry_match

val cbor_det_mk_map_from_array_safe () : mk_map_from_array_safe_t cbor_det_match cbor_det_map_entry_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_map_from_array' = mk_map_from_array' cbor_det_mk_map_from_array

(* Destructors *)

val cbor_det_equal () : equal_t cbor_det_match
val cbor_det_major_type () : get_major_type_t cbor_det_match
val cbor_det_read_simple_value () : read_simple_value_t cbor_det_match
val cbor_det_elim_simple () : elim_simple_t cbor_det_match
val cbor_det_read_uint64 () : read_uint64_t cbor_det_match
val cbor_det_elim_int64 () : elim_int64_t cbor_det_match
val cbor_det_get_string_length () : get_string_length_t cbor_det_match
val cbor_det_get_tagged_tag () : get_tagged_tag_t cbor_det_match
val cbor_det_get_tagged_payload () : get_tagged_payload_t cbor_det_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_get_string_t
= (x: cbor_det_t) ->
  (#p: perm) ->
  (#y: Ghost.erased Spec.cbor) ->
  stt (AP.ptr FStar.UInt8.t)
    (cbor_det_match p x y ** pure (Spec.CString? (Spec.unpack y)))
    (fun res -> exists* p' v' .
      pts_to res #p' v' **
      Trade.trade
        (pts_to res #p' v')
        (cbor_det_match p x y) **
      pure (get_string_post y v')
    )

val cbor_det_get_string () : cbor_det_get_string_t


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

val cbor_det_map_get () : map_get_by_ref_t cbor_det_match

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_map_get_gen () : map_get_t cbor_det_match = map_get_as_option (cbor_det_map_get ())

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_tag_to_array_t
=
  (tag: U64.t) ->
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v ** pure (SZ.v out_len == Seq.length v))
  (fun res -> exists* v . pts_to out v ** pure (
     cbor_det_serialize_tag_postcond tag out_len res v
  ))

val cbor_det_serialize_tag_to_array (_: unit) : cbor_det_serialize_tag_to_array_t

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_array_to_array_t
= (len: U64.t) ->
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  (l: Ghost.erased (list Spec.cbor)) ->
  (off: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_det_serialize_array_precond len l off v /\
      Seq.length v == SZ.v out_len
    )
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_det_serialize_array_postcond l res v /\
      Seq.length v == SZ.v out_len
    )
  )

val cbor_det_serialize_array_to_array (_: unit) : cbor_det_serialize_array_to_array_t

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_string_to_array_t
= (ty: major_type_byte_string_or_text_string) ->
  (off: U64.t) ->
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
  (pts_to out v **
    pure (cbor_det_serialize_string_precond ty off v /\
      Seq.length v == SZ.v out_len
    )
  )
  (fun res -> exists* v' .
    pts_to out v' **
    pure (cbor_det_serialize_string_postcond ty off v res v' /\
      Seq.length v' == SZ.v out_len
    )
  )

val cbor_det_serialize_string_to_array (_: unit) : cbor_det_serialize_string_to_array_t

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_map_insert_to_array_t =
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  (m: Ghost.erased Spec.cbor_map) ->
  (off2: SZ.t) ->
  (key: Ghost.erased Spec.cbor) ->
  (off3: SZ.t) ->
  (value: Ghost.erased Spec.cbor) ->
  stt bool
    (exists* v .
      pts_to out v **
      pure (cbor_det_serialize_map_insert_pre m off2 key off3 value v /\
        SZ.v out_len == Seq.length v
      )
    )
    (fun res -> exists* v .
      pts_to out v **
      pure (cbor_det_serialize_map_insert_post m key value res v /\
        SZ.v out_len == Seq.length v
      )
    )

val cbor_det_serialize_map_insert_to_array (_: unit) : cbor_det_serialize_map_insert_to_array_t

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_serialize_map_to_array_t =
  (len: U64.t) ->
  (out: AP.ptr U8.t) ->
  (out_len: SZ.t) ->
  (l: Ghost.erased (Spec.cbor_map)) ->
  (off: SZ.t) ->
  stt SZ.t
  (exists* v . pts_to out v **
    pure (cbor_det_serialize_map_precond len l off v /\
      SZ.v out_len == Seq.length v
    )
  )
  (fun res -> exists* v .
    pts_to out v **
    pure (cbor_det_serialize_map_postcond l res v /\
      SZ.v out_len == Seq.length v
    )
  )

val cbor_det_serialize_map_to_array (_: unit) : cbor_det_serialize_map_to_array_t
