module CBOR.SteelST.Map
include CBOR.SteelST.Map.Base
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

val constr_cbor_map
  (#c': Ghost.erased (Seq.seq cbor_map_entry))
  (#v': Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (a: A.array cbor_map_entry)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: STT cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_map_match full_perm c' v')
    (fun res ->
      raw_data_item_match full_perm res (Cbor.Map v') `star`
      (raw_data_item_match full_perm res (Cbor.Map v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_map_match full_perm c' v')
      )
    )

val cbor_map_iterator_init
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Map? v })
: STT cbor_map_iterator_t
    (raw_data_item_match p a v)
    (fun i ->
      cbor_map_iterator_match p i (Cbor.Map?.v v) `star`
      (cbor_map_iterator_match p i (Cbor.Map?.v v) `implies_`
        raw_data_item_match p a v)
    )

val cbor_map_iterator_is_done
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (i: cbor_map_iterator_t)
: ST bool
    (cbor_map_iterator_match p i l)
    (fun _ -> cbor_map_iterator_match p i l)
    True
    (fun res -> res == Nil? l)

val cbor_map_iterator_next
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (#i: Ghost.erased cbor_map_iterator_t)
  (pi: R.ref cbor_map_iterator_t { Cons? l })
: STT cbor_map_entry
    (R.pts_to pi full_perm i `star` cbor_map_iterator_match p i l)
    (fun c -> exists_ (fun i' ->
      R.pts_to pi full_perm i' `star`
      raw_data_item_map_entry_match p c (List.Tot.hd l) `star`
      cbor_map_iterator_match p i' (List.Tot.tl l) `star`
      ((raw_data_item_map_entry_match p c (List.Tot.hd l) `star`
        cbor_map_iterator_match p i' (List.Tot.tl l)) `implies_`
        cbor_map_iterator_match p i l
      )
    ))
