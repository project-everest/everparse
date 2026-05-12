module CBOR.Pulse.Raw.EverParse.Serialize

open Pulse.Lib.Pervasives
open CBOR.Spec.Raw.Base
open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Type
open LowParse.Pulse.Base
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module U8 = FStar.UInt8

(* Header writer / sizer: needed by clients that build CBOR fragments
   (e.g. fragment serializers for tag, array, string, map_insert, map). *)

val write_header : l2r_leaf_writer serialize_header

val size_header : leaf_compute_remaining_size serialize_header

val cbor_serialize
  (f64: squash SZ.fits_u64)
  (x: cbor_raw)
  (output: S.slice U8.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
: stt SZ.t
    (exists* v . cbor_raw_match pm x y ** pts_to output v ** pure (Seq.length (serialize_cbor y) <= SZ.v (S.len output)))
    (fun res -> exists* v . cbor_raw_match pm x y ** pts_to output v ** pure (
      let s = serialize_cbor y in
      SZ.v res == Seq.length s /\
      (exists v' . v `Seq.equal` (s `Seq.append` v'))
    ))

let cbor_size_post
  (bound: SZ.t)
  (y: raw_data_item)
  (res: SZ.t)
: Tot prop
= let s = Seq.length (serialize_cbor y) in
  (SZ.v res == 0 <==> s > SZ.v bound) /\
  (SZ.v res > 0 ==> SZ.v res == s)

val cbor_size
  (f64: squash SZ.fits_u64)
  (x: cbor_raw)
  (bound: SZ.t)
  (#y: Ghost.erased raw_data_item)
  (#pm: perm)
: stt SZ.t
    (cbor_raw_match pm x y)
    (fun res -> cbor_raw_match pm x y ** pure (cbor_size_post bound y res))
