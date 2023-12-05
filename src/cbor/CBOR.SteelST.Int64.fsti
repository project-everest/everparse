module CBOR.SteelST.Int64
include CBOR.SteelST.Match
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

val cbor_destr_int64
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match p c (Ghost.reveal va))
    (fun _ -> raw_data_item_match p c (Ghost.reveal va))
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.cbor_int_type c'.cbor_int_value
    )

val cbor_constr_int64
  (ty: Cbor.major_type_uint64_or_neg_int64)
  (value: U64.t)
: STT cbor
    emp
    (fun c -> raw_data_item_match full_perm c (Cbor.Int64 ty value))
