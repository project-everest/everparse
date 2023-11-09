module CBOR.SteelST.Map.Base
include CBOR.SteelST.Match
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

val cbor_map_length
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST U64.t
    (raw_data_item_match p a v)
    (fun _ -> raw_data_item_match p a v)
    (Cbor.Map? v)
    (fun res ->
      Cbor.Map? v /\
      U64.v res == List.Tot.length (Cbor.Map?.v v)
    )

val dummy_cbor_map_iterator: cbor_map_iterator_t

val cbor_map_iterator_match
  (p: perm)
  (i: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
