module CBOR.SteelST.Array
include CBOR.SteelST.Type
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

val constr_cbor_array
  (#c': Ghost.erased (Seq.seq cbor))
  (#v': Ghost.erased (list Cbor.raw_data_item))
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: STT cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match full_perm c' v')
    (fun res ->
      raw_data_item_match full_perm res (Cbor.Array v') `star`
      (raw_data_item_match full_perm res (Cbor.Array v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_array_match full_perm c' v')
      )
    )

[@@__reduce__]
let maybe_cbor_array
  (v: Cbor.raw_data_item)
: GTot (list Cbor.raw_data_item)
= match v with
  | Cbor.Array l -> l
  | _ -> []

val cbor_array_length
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST U64.t
    (raw_data_item_match p a v)
    (fun _ -> raw_data_item_match p a v)
    (Cbor.Array? v)
    (fun res ->
      Cbor.Array? v /\
      U64.v res == List.Tot.length (Cbor.Array?.v v)
    )

val cbor_array_index
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (i: SZ.t {
    Cbor.Array? v /\
    SZ.v i < List.Tot.length (Cbor.Array?.v v)
  })
: STT cbor
    (raw_data_item_match p a v)
    (fun a' ->
      raw_data_item_match p a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `star`
      (raw_data_item_match p a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `implies_`
        raw_data_item_match p a v)
    )

val cbor_array_iterator_t: Type0

val dummy_cbor_array_iterator: cbor_array_iterator_t

val cbor_array_iterator_match
  (p: perm)
  (i: cbor_array_iterator_t)
  (l: list Cbor.raw_data_item)
: Tot vprop

val cbor_array_iterator_init
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Array? v })
: STT cbor_array_iterator_t
    (raw_data_item_match p a v)
    (fun i ->
      cbor_array_iterator_match p i (Cbor.Array?.v v) `star`
      (cbor_array_iterator_match p i (Cbor.Array?.v v) `implies_`
        raw_data_item_match p a v)
    )

val cbor_array_iterator_is_done
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (i: cbor_array_iterator_t)
: ST bool
    (cbor_array_iterator_match p i l)
    (fun _ -> cbor_array_iterator_match p i l)
    True
    (fun res -> res == Nil? l)

val cbor_array_iterator_next
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (#i: Ghost.erased cbor_array_iterator_t)
  (pi: R.ref cbor_array_iterator_t { Cons? l })
: STT cbor
    (R.pts_to pi full_perm i `star` cbor_array_iterator_match p i l)
    (fun c -> exists_ (fun i' ->
      R.pts_to pi full_perm i' `star`
      raw_data_item_match p c (List.Tot.hd l) `star`
      cbor_array_iterator_match p i' (List.Tot.tl l) `star`
      ((raw_data_item_match p c (List.Tot.hd l) `star`
        cbor_array_iterator_match p i' (List.Tot.tl l)) `implies_`
        cbor_array_iterator_match p i l
      )
    ))

val read_cbor_array
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (#vdest: Ghost.erased (Seq.seq cbor))
  (dest: A.array cbor) // it is the user's responsibility to allocate the array properly
  (len: U64.t)
: ST (A.array cbor)
    (raw_data_item_match p a v `star`
      A.pts_to dest full_perm vdest
    )
    (fun res -> exists_ (fun vres ->
      A.pts_to res p vres `star`
      raw_data_item_array_match p vres (maybe_cbor_array v) `star`
      ((A.pts_to res p vres `star`
        raw_data_item_array_match p vres (maybe_cbor_array v)) `implies_` (
        raw_data_item_match p a v `star`
        (exists_ (A.pts_to dest full_perm))
      ))
    ))
    (Cbor.Array? v /\
      (U64.v len == A.length dest \/ U64.v len == Seq.length vdest) /\
      U64.v len == List.Tot.length (Cbor.Array?.v v)
    )
    (fun res ->
      Cbor.Array? v /\
      U64.v len == A.length dest /\
      U64.v len == A.length res
    )
