module CBOR.Pulse.Raw.EverParse.Serialized.Base
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives

open Pulse.Lib.Slice open Pulse.Lib.Pervasives open Pulse.Lib.Trade
open CBOR.Spec.Raw.EverParse
open LowParse.Spec.Base open LowParse.Pulse.Base

module PM = Pulse.Lib.SeqMatch
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64

val cbor_read
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased raw_data_item)
: stt cbor_raw
  (requires
    pts_to_serialized serialize_raw_data_item input #pm v)
  (ensures fun res ->
      cbor_match 1.0R res v **
      trade (cbor_match 1.0R res v) (pts_to_serialized serialize_raw_data_item input #pm v)
  )
