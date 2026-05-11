module CBOR.Pulse.Raw.EverParse.Det.Impl

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Base
open CBOR.Pulse.API.Det.Type

module Spec = CBOR.Spec.API.Format
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util

val cbor_det_match: perm -> cbor_det_t -> Spec.cbor -> slprop

val cbor_det_share (_: unit) : share_t cbor_det_match
val cbor_det_gather (_: unit) : gather_t cbor_det_match

val cbor_det_size
  (x: cbor_det_t)
  (bound: SZ.t)
  (#y: Ghost.erased Spec.cbor)
  (#pm: perm)
: stt SZ.t
    (cbor_det_match pm x y)
    (fun res -> cbor_det_match pm x y ** pure (cbor_det_size_post bound y res))

val cbor_det_equal (_: unit) : equal_t cbor_det_match

val cbor_det_major_type (_: unit) : get_major_type_t cbor_det_match

val cbor_det_get_tagged_payload (_: unit) : get_tagged_payload_t cbor_det_match

val cbor_det_mk_simple_value (_: unit) : mk_simple_t cbor_det_match
val cbor_det_mk_int64 (_: unit) : mk_int64_t cbor_det_match
