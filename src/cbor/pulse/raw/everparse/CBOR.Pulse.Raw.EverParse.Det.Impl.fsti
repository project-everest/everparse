module CBOR.Pulse.Raw.EverParse.Det.Impl

open Pulse.Lib.Pervasives
open CBOR.Pulse.API.Base
open CBOR.Pulse.API.Det.Type

module Spec = CBOR.Spec.API.Format
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
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

(* Field readers *)
val cbor_det_read_simple_value (_: unit) : read_simple_value_t cbor_det_match
val cbor_det_read_uint64 (_: unit) : read_uint64_t cbor_det_match
val cbor_det_get_string_length (_: unit) : get_string_length_t cbor_det_match
val cbor_det_get_tagged_tag (_: unit) : get_tagged_tag_t cbor_det_match
val cbor_det_get_array_length (_: unit) : get_array_length_t cbor_det_match
val cbor_det_get_map_length (_: unit) : get_map_length_t cbor_det_match

(* Elim functions *)
val cbor_det_elim_simple (_: unit) : elim_simple_t cbor_det_match
val cbor_det_elim_int64 (_: unit) : elim_int64_t cbor_det_match

(* Reset perm *)
val cbor_det_reset_perm (_: unit) : reset_perm_t u#0 u#0 cbor_det_match

(* Constructors *)
val cbor_det_mk_tagged (_: unit) : mk_tagged_t cbor_det_match
val cbor_det_mk_string (_: unit) : mk_string_t cbor_det_match
