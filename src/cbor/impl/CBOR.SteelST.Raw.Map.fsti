module CBOR.SteelST.Raw.Map
include CBOR.SteelST.Raw.Base
open CBOR.SteelST.Raw.Validate
open LowParse.SteelST.Combinators
open LowParse.SteelST.Assoc
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.ValidateAndRead
open LowParse.SteelST.SeqBytes
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module NL = LowParse.SteelST.VCList.Sorted
module SB = LowParse.SteelST.SeqBytes
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module I16 = FStar.Int16
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

#set-options "--ide_id_info_off"

(* 4.2 Ordering of map keys *)

inline_for_extraction
noextract
val map_entry_order_impl
  (#kkey: Ghost.erased parser_kind)
  (#key: Type0)
  (pkey: parser kkey key)
  (#key_order: Ghost.erased (key -> key -> bool))
  (key_order_impl: NL.order_impl pkey key_order)
  (#kvalue: Ghost.erased parser_kind)
  (#value: Type0)
  (pvalue: parser kvalue value)
: Pure (NL.order_impl (pkey `nondep_then` pvalue) (map_entry_order key_order value))
    (requires (kkey.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))

unfold
let get_raw_data_item_payload_map_post
  (va: v parse_raw_data_item_kind raw_data_item)
  (vh: v (get_parser_kind parse_header) header)
  (n: nat)
  (vc: v (NL.parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) (NL.nlist n (raw_data_item & raw_data_item)))
: GTot prop
=
        let (| h, c |) = synth_raw_data_item_recip va.contents in
        let (| b, x |) = h in
        // order of the following conjuncts matters for typechecking
        vh.contents == h /\
        n == UInt64.v (argument_as_uint64 b x) /\
        va.contents == Map vc.contents /\
        vc.contents == c /\
        AP.merge_into (array_of' vh) (array_of' vc) (array_of va)

val get_raw_data_item_payload_map
  (#opened: _)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vh -> exists_ (fun (n: nat) -> exists_ (fun vc ->
      aparse parse_header a vh `star`
      aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) a' vc `star`
      pure (get_raw_data_item_payload_map_post va vh n vc)
    ))))
    (Map? va.contents)
    (fun _ -> True)

val intro_raw_data_item_map
  (#opened: _)
  (#vh: v (get_parser_kind parse_header) header)
  (h: byte_array)
  (#n: nat)
  (#vc: v (NL.parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) (NL.nlist n (raw_data_item & raw_data_item)))
  (c: byte_array)
: STGhost (v parse_raw_data_item_kind raw_data_item) opened
    (aparse parse_header h vh `star`
      aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) c vc
    )
    (fun va -> aparse parse_raw_data_item h va)
    (
      let (| b, x |) = vh.contents in
      let (major_type, _) = b in
      n == UInt64.v (argument_as_uint64 b x) /\
      major_type == get_major_type (Map vc.contents) /\
      AP.adjacent (array_of' vh) (array_of' vc)
    )
    (fun va ->
      get_raw_data_item_payload_map_post va vh n vc
    )

noextract
let focus_map_postcond
  (va: v parse_raw_data_item_kind raw_data_item)
  (n: nat)
  (va': v (NL.parse_nlist_kind n (and_then_kind parse_raw_data_item_kind parse_raw_data_item_kind)) (NL.nlist n (raw_data_item & raw_data_item)))
: Tot prop
= Map? va.contents /\
  va'.contents == Map?.v va.contents

val focus_map_with_ghost_length
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
  (n: Ghost.erased nat)
: ST byte_array
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun va' ->
      aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) a' va' `star`

      (aparse (NL.parse_nlist n (parse_raw_data_item `nondep_then` parse_raw_data_item)) a' va' `implies_`
        aparse parse_raw_data_item a va) `star`
      pure (focus_map_postcond va n va')
    ))
    (Map? va.contents /\
      Ghost.reveal n == List.Tot.length (Map?.v va.contents)
    )
    (fun _ -> True)

inline_for_extraction
noextract
val check_data_item_wf_head
  (#order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (order_impl: NL.order_impl parse_raw_data_item order)
  (sq: squash (SZ.fits_u64))
: Tot (pred_recursive_base_t serialize_raw_data_item_param (data_item_wf_head order))

inline_for_extraction
noextract
val check_raw_data_item
  (#p: Ghost.erased (raw_data_item -> bool))
  (p_impl: pred_recursive_base_t serialize_raw_data_item_param p)
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST bool
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    True
    (fun res -> res == holds_on_raw_data_item p va.contents)

inline_for_extraction
noextract
val validate_raw_data_item_filter
  (#p: Ghost.erased (raw_data_item -> bool))
  (p_impl: pred_recursive_base_t serialize_raw_data_item_param p)
: Tot (validator (parse_filter parse_raw_data_item (holds_on_raw_data_item p)))

inline_for_extraction
noextract
val validate_data_item
  (#order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (order_impl: NL.order_impl parse_raw_data_item order)
: Tot (validator (parse_data_item order))

val deterministically_encoded_cbor_map_key_order_impl
: NL.order_impl parse_raw_data_item deterministically_encoded_cbor_map_key_order

val validate_deterministically_encoded_cbor_data_item
: validator (parse_data_item deterministically_encoded_cbor_map_key_order)

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val validate_canonical_cbor_data_item
: validator (parse_data_item canonical_cbor_map_key_order)

val jump_data_item
  (order: Ghost.erased (raw_data_item -> raw_data_item -> bool))
: Tot (jumper (parse_data_item order))

(* Comparisons with unserialized values *)

(*
val lex_compare_with_header
  (ty: Ghost.erased major_type_t { ty `U8.lt` cbor_major_type_simple_value })
  (x: U64.t)
  (b: U8.t)
  (#vh: v (get_parser_kind parse_header) header)
  (a: byte_array)
: ST I16.t
    (aparse parse_header a vh)
    (fun _ -> aparse parse_header a vh)
    (b == get_uint64_as_initial_byte ty x)
    (fun i ->
      let s0 = serialize serialize_header (uint64_as_argument ty x) in
      let s = serialize serialize_header vh.contents in
      bytes_lex_compare s0 s `same_sign` I16.v i
    )
*)
