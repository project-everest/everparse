module CBOR.SteelST.Raw.Validate
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

module R = Steel.ST.Reference
module I = LowParse.SteelST.Int
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module NL = LowParse.SteelST.VCList.Sorted
module SB = LowParse.SteelST.SeqBytes

inline_for_extraction
noextract
val read_and_jump_initial_byte : read_and_jump parse_initial_byte

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val jump_header : jumper parse_header

val jump_leaf
: jumper parse_leaf

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val read_major_type
  (#va: v parse_raw_data_item_kind raw_data_item)
  (a: byte_array)
: ST byte
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    True
    (fun res -> res == get_major_type va.contents)

val read_header_argument_as_uint64
  (#va: v (get_parser_kind parse_header) header)
  (a: byte_array)
: ST UInt64.t
    (aparse parse_header a va)
    (fun _ -> aparse parse_header a va)
    True
    (fun res ->
      res == get_header_argument_as_uint64 va.contents
    )

inline_for_extraction
noextract
let read_argument_as_uint64_t =
  (#va: v parse_raw_data_item_kind raw_data_item) ->
  (a: byte_array) ->
  ST UInt64.t
    (aparse parse_raw_data_item a va)
    (fun _ -> aparse parse_raw_data_item a va)
    True
    (fun res ->
      let (| (| b, x |), _ |) = synth_raw_data_item_recip va.contents in
      res == argument_as_uint64 b x
    )

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val read_argument_as_uint64 : read_argument_as_uint64_t

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val validate_raw_data_item
: validator parse_raw_data_item

val jump_count_remaining_data_items
: (jump_recursive_step_count parse_raw_data_item_param)

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val jump_raw_data_item
: jumper parse_raw_data_item
