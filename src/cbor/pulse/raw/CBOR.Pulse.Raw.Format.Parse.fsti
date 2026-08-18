module CBOR.Pulse.Raw.Format.Parse
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Format
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module R = CBOR.Spec.Raw.Optimal

val cbor_validate
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      if SZ.v res = 0
      then (~ (exists v1 v2 . Ghost.reveal v == serialize_cbor v1 `Seq.append` v2))
      else exists v1 v2 . Ghost.reveal v == serialize_cbor v1 `Seq.append` v2 /\ SZ.v res == Seq.length (serialize_cbor v1)
    ))

let cbor_validate_det_post
  (v: Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
=
      if SZ.v res = 0
      then (~ (exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2 /\ R.raw_data_item_ints_optimal v1 /\ R.raw_data_item_sorted deterministically_encoded_cbor_map_key_order v1))
      else exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2 /\ SZ.v res == Seq.length (serialize_cbor v1) /\ R.raw_data_item_ints_optimal v1 /\ R.raw_data_item_sorted deterministically_encoded_cbor_map_key_order v1

val cbor_validate_det
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (pts_to input #pm v)
    (fun res -> pts_to input #pm v ** pure (
      cbor_validate_det_post v res
    ))

val cbor_parse
  (input: slice U8.t)
  (len: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
: stt cbor_raw
    (pts_to input #pm v ** pure (
      exists v1 v2 . Ghost.reveal v == serialize_cbor v1 `Seq.append` v2 /\ SZ.v len == Seq.length (serialize_cbor v1)
    ))
    (fun res -> exists* v' .
      cbor_match 1.0R res v' **
      trade (cbor_match 1.0R res v') (pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == serialize_cbor v'
    ))

let cbor_jump_pre
  (off: SZ.t)
  (c: raw_data_item)
  (v: Seq.seq U8.t)
: Tot prop
= let s = serialize_cbor c in
  let off' = SZ.v off + Seq.length s in
  off' <= Seq.length v /\
  Seq.slice v (SZ.v off) off' == s

inline_for_extraction
let cbor_jump_t =
  (input: slice U8.t) ->
  (off: SZ.t) ->
  (c: Ghost.erased raw_data_item) ->
  (#pm: perm) ->
  (#v: Ghost.erased (Seq.seq U8.t)) ->
  stt SZ.t
    (pts_to input #pm v ** pure (
      cbor_jump_pre off c v
    ))
    (fun res ->
      pts_to input #pm v ** pure (
      SZ.v res == SZ.v off + Seq.length (serialize_cbor c)
    ))

val cbor_jump (_: unit) : cbor_jump_t
