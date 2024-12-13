module CBOR.Pulse.API.Det.C
#lang-pulse
include CBOR.Pulse.API.Det.Common
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
      cbor_det_serialize_postcond y res v
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
      cbor_det_serialize_postcond y res v
    ))
{
  S.pts_to_len output;
  let len = S.len output;
  let ou = S.slice_to_arrayptr_intro output;
  let res = cbor_det_serialize x ou len;
  S.slice_to_arrayptr_elim ou;
  res
}

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_string_from_array_t =
  (ty: major_type_byte_string_or_text_string) ->
  (a: A.array U8.t) ->
  (len: U64.t) ->
  (#p: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt cbor_det_t
    (pts_to a #p v ** pure (
      Seq.length v == U64.v len /\
      (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v)
    ))
    (fun res -> exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade
        (cbor_det_match 1.0R res v')
        (pts_to a #p v) **
      pure (
        Spec.CString? (Spec.unpack v') /\
        Spec.CString?.typ (Spec.unpack v') == ty /\
        Ghost.reveal v == Spec.CString?.v (Spec.unpack v')
      )
    )

val cbor_det_mk_string_from_array (_: unit) : cbor_det_mk_string_from_array_t

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_array_from_array_t =
  (a: A.array cbor_det_t) ->
  (len: U64.t) ->
  (#pa: perm) ->
  (#va: Ghost.erased (Seq.seq cbor_det_t)) ->
  (#pv: perm) ->
  (#vv: Ghost.erased (list Spec.cbor)) ->
  stt cbor_det_t
    (A.pts_to a #pa va **
      PM.seq_list_match va vv (cbor_det_match pv) **
      pure (A.length a == U64.v len)
    )
    (fun res -> exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade
        (cbor_det_match 1.0R res v')
        (A.pts_to a #pa va **
          PM.seq_list_match va vv (cbor_det_match pv)
        ) **
        pure (
          Spec.CArray? (Spec.unpack v') /\
          Ghost.reveal vv == Spec.CArray?.v (Spec.unpack v')
        )
    )

val cbor_det_mk_array_from_array (_: unit) : cbor_det_mk_array_from_array_t

inline_for_extraction
noextract [@@noextract_to "krml"]
fn cbor_det_mk_array_from_array'
  (a: A.array cbor_det_t)
  (len: U64.t)
  (va0: Ghost.erased (Seq.seq cbor_det_t))
  (#pa: perm)
  (#va: Ghost.erased (Seq.seq cbor_det_t))
  (#pv: perm)
  (#vv: Ghost.erased (list Spec.cbor))
requires
    (A.pts_to a #pa va **
      PM.seq_list_match va0 vv (cbor_det_match pv) **
      pure (A.length a == U64.v len /\
        Seq.equal va0 va
      )
    )
returns res: cbor_det_t
ensures
    (exists* v' .
      cbor_det_match 1.0R res v' **
      Trade.trade
        (cbor_det_match 1.0R res v')
        (A.pts_to a #pa va **
          PM.seq_list_match va0 vv (cbor_det_match pv)
        ) **
        pure (
          Spec.CArray? (Spec.unpack v') /\
          Ghost.reveal vv == Spec.CArray?.v (Spec.unpack v')
        )
    )
{
  Trade.rewrite_with_trade
    (PM.seq_list_match va0 vv (cbor_det_match pv))
    (PM.seq_list_match va vv (cbor_det_match pv));
  let res = cbor_det_mk_array_from_array () a len;
  Trade.trans_concl_r _ _ _ (PM.seq_list_match va0 vv (cbor_det_match pv));
  res
}

val cbor_det_mk_map_from_array : mk_map_from_array_t cbor_det_match cbor_det_map_entry_match

inline_for_extraction
noextract [@@noextract_to "krml"]
let cbor_det_mk_map_from_array' = mk_map_from_array' cbor_det_mk_map_from_array

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

val cbor_det_map_get () : map_get_by_ref_t cbor_det_match

inline_for_extraction noextract [@@noextract_to "krml"]
let cbor_det_map_get_gen () : map_get_t cbor_det_match = map_get_as_option (cbor_det_map_get ())
