module CBOR.SteelST.Raw.Read
include CBOR.SteelST.Raw.Base
open LowParse.SteelST.Combinators
open LowParse.SteelST.Assoc
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.ValidateAndRead
open LowParse.SteelST.SeqBytes
open Steel.ST.GenElim

#set-options "--print_universes"

#set-options "--ide_id_info_off"

module AP = LowParse.SteelST.ArrayPtr
module I = LowParse.SteelST.Int
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module NL = LowParse.SteelST.VCList.Sorted
module SB = LowParse.SteelST.SeqBytes
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

(* Readers and accessors *)

(* Here we only retain the two cases for simple values. Otherwise, if
   we use the general-purpose jump_long_argument, F* extracts to
   `match B with A -> ...` with mismatching constructors, which neither F*
   nor Karamel eliminate as dead code.
 *)

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val read_simple_value
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST simple_value
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    (Simple? va.contents)
    (fun res -> va.contents == Simple res)

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val read_int64
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST U64.t
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    (Int64? va.contents)
    (fun res -> 
      match va.contents with
      | Int64 _ res' -> res == res'
      | _ -> False
    )

let intro_raw_data_item_string_pre
  (m: major_type_byte_string_or_text_string)
  (vh:  v (get_parser_kind parse_header) header)
  (vp: AP.v byte)
: GTot prop
= let (| b, arg |) = vh.contents in
  let (major_type, _) = b in
  major_type == m /\
  AP.adjacent (array_of vh) (AP.array_of vp) /\
  U64.v (argument_as_uint64 b arg) == Seq.length (AP.contents_of vp)

val intro_raw_data_item_string
  (#opened: _)
  (m: major_type_byte_string_or_text_string)
  (#vh: v (get_parser_kind parse_header) header)
  (ah: byte_array)
  (#vp: _)
  (ap: byte_array)
: STGhost (v parse_raw_data_item_kind raw_data_item) opened
    (aparse parse_header ah vh `star` AP.arrayptr ap vp)
    (fun v' -> aparse parse_raw_data_item ah v')
    (intro_raw_data_item_string_pre m vh vp)
    (fun v' ->
      let (| b, arg |) = vh.contents in
      AP.merge_into (array_of vh) (AP.array_of vp) (array_of v') /\
      U64.v (argument_as_uint64 b arg) == Seq.length (AP.contents_of vp) /\
      v'.contents == String m (AP.contents_of vp)
    )

let ghost_focus_string_post
  (va: v parse_raw_data_item_kind raw_data_item)
  (vp: AP.v byte)
: GTot prop
=
        FStar.UInt.fits (Seq.length (AP.contents_of vp)) U64.n /\
        begin match va.contents with
        | String _ contents ->  contents == AP.contents_of vp
        | _ -> False
        end

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val focus_string
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST byte_array
    (aparse parse_raw_data_item a va)
    (fun a' -> exists_ (fun vp ->
      AP.arrayptr a' vp `star`
      pure (
        ghost_focus_string_post va vp
      ) `star`
      (AP.arrayptr a' vp `implies_` aparse parse_raw_data_item a va)
    ))
    (String? va.contents)
    (fun _ -> True)
