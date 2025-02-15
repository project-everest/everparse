module CBOR.Pulse.Raw.Format.Serialize
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Format
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module MS = Pulse.Lib.MutableSlice

val cbor_serialize
  (x: cbor_raw)
  (output: MS.slice U8.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
: stt SZ.t
    (exists* v . cbor_match pm x y ** pts_to output v ** pure (Seq.length (serialize_cbor y) <= SZ.v (MS.len output)))
    (fun res -> exists* v . cbor_match pm x y ** pts_to output v ** pure (
      let s = serialize_cbor y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    ))

noextract [@@noextract_to "krml"]
let cbor_size_post
  (bound: SZ.t)
  (y: raw_data_item)
  (res: SZ.t)
: Tot prop
=
      let s = Seq.length (serialize_cbor y) in
      (SZ.v res == 0 <==> s > SZ.v bound) /\
      (SZ.v res > 0 ==> SZ.v res == s)

val cbor_size
  (x: cbor_raw)
  (bound: SZ.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
: stt SZ.t
    (cbor_match pm x y)
    (fun res -> cbor_match pm x y ** pure (
      cbor_size_post bound y res
    ))
