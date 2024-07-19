module CBOR.Pulse.Raw.Parse
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Order
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT

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
      (cbor_match 1.0R res v' @==> pts_to input #pm v) ** pure (
        SZ.v len <= Seq.length v /\
        Seq.slice v 0 (SZ.v len) == serialize_cbor v'
    ))
