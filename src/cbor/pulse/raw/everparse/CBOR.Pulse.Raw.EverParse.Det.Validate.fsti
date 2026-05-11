module CBOR.Pulse.Raw.EverParse.Det.Validate

open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Format
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module SZ = FStar.SizeT
module RV = CBOR.Spec.Raw.Optimal
module RF = CBOR.Spec.Raw.Format
module S = Pulse.Lib.Slice

let cbor_validate_det_post
  (v: Seq.seq FStar.UInt8.t)
  (res: SZ.t)
: Tot prop
=
      if SZ.v res = 0
      then (~ (exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2 /\ RV.raw_data_item_ints_optimal v1 /\ RV.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order v1))
      else (exists v1 v2 . v == serialize_cbor v1 `Seq.append` v2 /\ RV.raw_data_item_ints_optimal v1 /\ RV.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order v1 /\ SZ.v res == Seq.length (serialize_cbor v1))

val cbor_validate_det
  (input: slice FStar.UInt8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq FStar.UInt8.t))
: stt SZ.t
  (requires pts_to input #pm v)
  (ensures fun res -> pts_to input #pm v ** pure (cbor_validate_det_post v res))
