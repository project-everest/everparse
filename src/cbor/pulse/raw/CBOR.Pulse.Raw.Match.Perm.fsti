module CBOR.Pulse.Raw.Match.Perm
include CBOR.Pulse.Raw.Match
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module PM = Pulse.Lib.SeqMatch
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Trade = Pulse.Lib.Trade.Util

val cbor_raw_share
  (p: perm)
  (c: cbor_raw)
  (r: raw_data_item)
: stt_ghost unit emp_inames
  (
    cbor_match p c r
  )
  (fun _ ->
    cbor_match (p /. 2.0R) c r **
    cbor_match (p /. 2.0R) c r
  )

val cbor_raw_gather
  (p1: perm)
  (c: cbor_raw)
  (r1: raw_data_item)
  (p2: perm)
  (r2: raw_data_item)
: stt_ghost unit emp_inames
  (
    cbor_match p1 c r1 **
    cbor_match p2 c r2
  )
  (fun _ ->
    cbor_match (p1 +. p2) c r1 **
    pure (r1 == r2)
  )
