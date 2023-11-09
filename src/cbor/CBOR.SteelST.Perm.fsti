module CBOR.SteelST.Perm
include CBOR.SteelST.Match

open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

val cbor_gather
  (#opened: _)
  (c: cbor)
  (v1 v2: Cbor.raw_data_item)
  (p1 p2: perm)
: STGhost unit opened
    (raw_data_item_match p1 c v1 `star` raw_data_item_match p2 c v2)
    (fun _ -> raw_data_item_match (p1 `sum_perm` p2) c v1)
    True
    (fun _ -> v1 == v2)

val cbor_share
  (#opened: _)
  (c: cbor)
  (v1: Cbor.raw_data_item)
  (p p1 p2: perm)
: STGhost unit opened
    (raw_data_item_match p c v1)
    (fun _ -> raw_data_item_match p1 c v1 `star` raw_data_item_match p2 c v1)
    (p == p1 `sum_perm` p2)
    (fun _ -> True)
