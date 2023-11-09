module CBOR.SteelST.Tagged
include CBOR.SteelST.Match
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

[@@__reduce__]
let maybe_cbor_tagged_tag
  (v: Cbor.raw_data_item)
: GTot U64.t
= match v with
  | Cbor.Tagged t _ -> t
  | _ -> 0uL // dummy

[@@__reduce__]
let maybe_cbor_tagged_payload
  (v: Cbor.raw_data_item)
: GTot Cbor.raw_data_item
= match v with
  | Cbor.Tagged _ l -> l
  | _ -> Cbor.dummy_raw_data_item

noeq
type cbor_tagged = {
  cbor_tagged_tag: U64.t;
  cbor_tagged_payload: cbor;
}

val destr_cbor_tagged
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_tagged
    (raw_data_item_match p a v)
    (fun res ->
      raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v) `star`
      (raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v) `implies_`
        raw_data_item_match p a v
      )
    )
    (Cbor.Tagged? v)
    (fun res ->
      Cbor.Tagged? v /\
      res.cbor_tagged_tag == Cbor.Tagged?.tag v
    )

val constr_cbor_tagged
  (#c': Ghost.erased (cbor))
  (#v': Ghost.erased (Cbor.raw_data_item))
  (tag: U64.t)
  (a: R.ref cbor)
: STT cbor
    (R.pts_to a full_perm c' `star`
      raw_data_item_match full_perm c' v')
    (fun res ->
      raw_data_item_match full_perm res (Cbor.Tagged tag v') `star`
      (raw_data_item_match full_perm res (Cbor.Tagged tag v') `implies_`
        (R.pts_to a full_perm c' `star`
          raw_data_item_match full_perm c' v')
      )
    )
