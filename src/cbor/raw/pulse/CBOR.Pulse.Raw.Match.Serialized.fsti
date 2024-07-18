module CBOR.Pulse.Raw.Match.Serialized
include CBOR.Pulse.Raw.Type
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT

val cbor_match_serialized_payload_array
  (c: cbor_serialized)
  (p: perm)
  (r: list raw_data_item)
: Tot vprop

val cbor_match_serialized_payload_map
  (c: cbor_serialized)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
: Tot vprop

val cbor_match_serialized_payload_tagged
  (c: cbor_serialized)
  (p: perm)
  (r: raw_data_item)
: Tot vprop

(*
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
*)
