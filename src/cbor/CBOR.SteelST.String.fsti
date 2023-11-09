module CBOR.SteelST.String
include CBOR.SteelST.Match
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

val destr_cbor_string
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: STT cbor_string
    (raw_data_item_match p c (Ghost.reveal va))
    (fun c' -> exists_ (fun vc' -> exists_ (fun p' ->
      A.pts_to c'.cbor_string_payload p' vc' `star`
      (A.pts_to c'.cbor_string_payload p' vc' `implies_` raw_data_item_match p c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.cbor_string_length == Seq.length vc' /\
        c'.cbor_string_type == Cbor.String?.typ va /\
        vc' == Cbor.String?.v va
    ))))

val constr_cbor_string
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (typ: Cbor.major_type_byte_string_or_text_string)
  (a: A.array U8.t)
  (len: U64.t {
    U64.v len == Seq.length va
  })
: STT cbor
    (A.pts_to a p va)
    (fun c' ->
      raw_data_item_match full_perm c' (Cbor.String typ va) `star`
      (raw_data_item_match full_perm c' (Cbor.String typ va) `implies_`
        A.pts_to a p va
      )
    )
