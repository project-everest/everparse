module CBOR.SteelST.Raw.Array
include CBOR.SteelST.Raw.Base
open CBOR.SteelST.Raw.Validate
open LowParse.SteelST.Combinators
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.ValidateAndRead
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module NL = LowParse.SteelST.VCList.Sorted
module U8 = FStar.UInt8
module U64 = FStar.UInt64

unfold
let get_raw_data_item_payload_array_post
  (va: v parse_raw_data_item_kind raw_data_item)
  (vh: v (get_parser_kind parse_header) header)
  (n: nat)
  (vc: v (NL.parse_nlist_kind n parse_raw_data_item_kind) (NL.nlist n raw_data_item))
: GTot prop
=
        let (| h, c |) = synth_raw_data_item_recip va.contents in
        let (| b, x |) = h in
        // order of the following conjuncts matters for typechecking
        vh.contents == h /\
        n == UInt64.v (argument_as_uint64 b x) /\
        va.contents == Array vc.contents /\
        vc.contents == c /\
        AP.merge_into (array_of' vh) (array_of' vc) (array_of va)

val get_raw_data_item_payload_array
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vh -> exists_ (fun (n: nat) -> exists_ (fun vc ->
      aparse parse_header a vh `star`
      aparse (NL.parse_nlist n parse_raw_data_item) a' vc `star`
      pure (get_raw_data_item_payload_array_post va vh n vc)
    ))))
    (Array? va.contents)
    (fun _ -> True)

val intro_raw_data_item_array
  (#opened: _)
  (#vh: v (get_parser_kind parse_header) header)
  (h: byte_array)
  (#n: nat)
  (#vc: v (NL.parse_nlist_kind n parse_raw_data_item_kind) (NL.nlist n raw_data_item))
  (c: byte_array)
: STGhost (v parse_raw_data_item_kind raw_data_item) opened
    (aparse parse_header h vh `star`
      aparse (NL.parse_nlist n parse_raw_data_item) c vc
    )
    (fun va -> aparse parse_raw_data_item h va)
    (
      let (| b, x |) = vh.contents in
      let (major_type, _) = b in
      n == UInt64.v (argument_as_uint64 b x) /\
      major_type == get_major_type (Array vc.contents) /\
      AP.adjacent (array_of' vh) (array_of' vc)
    )
    (fun va ->
      get_raw_data_item_payload_array_post va vh n vc
    )

let focus_array_with_ghost_length_post
  (n: nat)
  (va: v parse_raw_data_item_kind raw_data_item)
  (vres: v (NL.parse_nlist_kind n parse_raw_data_item_kind) (NL.nlist n raw_data_item))
: Tot prop
= Array? va.contents /\
  Array?.v va.contents == vres.contents

val focus_array_with_ghost_length
  (n: Ghost.erased nat)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST byte_array
    (aparse parse_raw_data_item a va)
    (fun res -> exists_ (fun vres ->
      aparse (NL.parse_nlist n parse_raw_data_item) res vres `star`
      (aparse (NL.parse_nlist n parse_raw_data_item) res vres `implies_`
        aparse parse_raw_data_item a va
      ) `star` pure (
      focus_array_with_ghost_length_post n va vres
    )))
    (Array? va.contents /\
      Ghost.reveal n == List.Tot.length (Array?.v va.contents)
    )
    (fun _ -> True)

[@@erasable]
noeq
type focus_array_res = {
  n: U64.t;
  l: v (NL.parse_nlist_kind (U64.v n) parse_raw_data_item_kind) (NL.nlist (U64.v n) raw_data_item);
  a: byte_array;
}

val focus_array
  (#n': Ghost.erased U64.t)
  (#a': Ghost.erased byte_array)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (pn: R.ref U64.t)
  (pa: R.ref byte_array)
  (a: byte_array)
: ST focus_array_res
    (aparse parse_raw_data_item a va `star`
      R.pts_to pn full_perm n' `star`
      R.pts_to pa full_perm a'
    )
    (fun res ->
      R.pts_to pn full_perm res.n `star`
      R.pts_to pa full_perm res.a `star`
      aparse (NL.parse_nlist (U64.v res.n) parse_raw_data_item) res.a res.l `star`
      (aparse (NL.parse_nlist (U64.v res.n) parse_raw_data_item) res.a res.l `implies_`
        aparse parse_raw_data_item a va
      )
    )
    (Array? va.contents)
    (fun res ->
      va.contents == Array res.l.contents
    )
