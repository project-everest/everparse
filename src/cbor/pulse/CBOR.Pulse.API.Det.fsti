module CBOR.Pulse.API.Det
include CBOR.Pulse.API.Det.Type
include CBOR.Pulse.API.Base
open Pulse.Lib.Pervasives
module Spec = CBOR.Spec.API.Format
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module PM = Pulse.Lib.SeqMatch

val cbor_det_match: perm -> cbor_det_t -> Spec.cbor -> slprop
val cbor_det_match_with_size: nat -> perm -> cbor_det_t -> Spec.cbor -> slprop

val cbor_det_match_with_size_eq:
  (sz: nat) ->
  (p: perm) ->
  (c: cbor_det_t) ->
  (v: Spec.cbor) ->
  stt_ghost unit emp_inames
    (cbor_det_match_with_size sz p c v)
    (fun _ -> cbor_det_match_with_size sz p c v **
      pure (sz == Seq.length (Spec.cbor_det_serialize v))
    )

val cbor_det_map_entry_match: perm -> cbor_det_map_entry_t -> Spec.cbor & Spec.cbor -> slprop

val cbor_det_mk_map () : mk_map_t cbor_det_match cbor_det_map_entry_match
