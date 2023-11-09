module CBOR.SteelST.SimpleValue
include CBOR.SteelST.Match
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

val destr_cbor_simple_value
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match p c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match p c (Ghost.reveal va)
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Simple c'
    )

val constr_cbor_simple_value
  (value: Cbor.simple_value)
: STT cbor
    emp
    (fun c -> raw_data_item_match full_perm c (Cbor.Simple value))
