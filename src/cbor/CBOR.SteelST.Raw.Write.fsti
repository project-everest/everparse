module CBOR.SteelST.Raw.Write
include CBOR.SteelST.Raw.Base
open CBOR.SteelST.Raw.Read
open LowParse.SteelST.Combinators
open LowParse.SteelST.Assoc
open LowParse.SteelST.Recursive
open LowParse.SteelST.BitSum
open LowParse.SteelST.ValidateAndRead
open LowParse.SteelST.SeqBytes
open Steel.ST.GenElim

module R = Steel.ST.Reference
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module NL = LowParse.SteelST.VCList.Sorted
module SB = LowParse.SteelST.SeqBytes
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module I16 = FStar.Int16
module U64 = FStar.UInt64

#set-options "--ide_id_info_off"

(* Writers *)

val write_initial_byte
  (t: major_type_t)
  (x: additional_info_t)
  (sq: squash (
    initial_byte_wf (t, (x, ()))
  ))
  (#va: AP.v byte)
  (a: byte_array)
: ST (v (get_parser_kind parse_initial_byte) initial_byte)
    (AP.arrayptr a va)
    (fun va' ->
      aparse parse_initial_byte a va'
    )
    (AP.length (AP.array_of va) == 1 /\
      AP.array_perm (AP.array_of va) == full_perm
    )
    (fun va' -> 
       array_of' va' == AP.array_of va /\
       va'.contents == mk_initial_byte t x
    )

inline_for_extraction
noextract
val write_initial_byte'
: exact_writer serialize_initial_byte

inline_for_extraction
noextract
val write_long_argument
  (b: initial_byte)
  (a: long_argument b)
: Tot (maybe_r2l_writer_for (serialize_long_argument b) a)

inline_for_extraction
noextract
val size_comp_long_argument
  (b: initial_byte)
  (a: long_argument b)
: Tot (size_comp_for (serialize_long_argument b) a)

inline_for_extraction
noextract
val l2r_write_long_argument
  (b: initial_byte)
  (a: long_argument b)
: Tot (l2r_writer_for (serialize_long_argument b) a)

inline_for_extraction
noextract
val write_header : maybe_r2l_writer serialize_header

inline_for_extraction
noextract
val size_comp_header : size_comp serialize_header

inline_for_extraction
noextract
val l2r_write_header : l2r_writer serialize_header

inline_for_extraction
noextract
val write_simple_value_as_argument
  (x: simple_value)
: Tot (maybe_r2l_writer_for serialize_header (simple_value_as_argument x))

inline_for_extraction
noextract
val size_comp_simple_value_as_argument
  (x: simple_value)
: Tot (size_comp_for serialize_header (simple_value_as_argument x))

inline_for_extraction
noextract
val l2r_write_simple_value_as_argument
  (x: simple_value)
: Tot (l2r_writer_for serialize_header (simple_value_as_argument x))

module W = LowParse.SteelST.R2LOutput

val maybe_r2l_write_simple_value
  (#opened: _)
  (x: simple_value)
  (#vout: _)
  (out: W.t)
  (success: bool)
: STGhostT unit opened
   (maybe_r2l_write serialize_header out vout (simple_value_as_argument x) success)
   (fun _ -> maybe_r2l_write serialize_raw_data_item out vout (Simple x) success)

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val write_simple_value
  (x: simple_value)
: Tot (maybe_r2l_writer_for serialize_raw_data_item (Simple x))

val write_uint64_as_argument
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
  (x: U64.t)
: Tot (maybe_r2l_writer_for serialize_header (uint64_as_argument ty x))

inline_for_extraction
noextract
val size_comp_simple_value_header
  (x: simple_value)
: Tot (size_comp_for serialize_header (simple_value_as_argument x))

val size_comp_simple_value
  (x: simple_value)
: Tot (size_comp_for serialize_raw_data_item (Simple x))

inline_for_extraction
noextract
val l2r_write_simple_value_header
  (x: simple_value)
: Tot (l2r_writer_for serialize_header (simple_value_as_argument x))

val l2r_write_simple_value
  (x: simple_value)
: Tot (l2r_writer_for serialize_raw_data_item (Simple x))

val size_comp_uint64_header
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
  (x: U64.t)
: Tot (size_comp_for serialize_header (uint64_as_argument ty x))

val size_comp_int64
  (ty: major_type_uint64_or_neg_int64)
  (x: U64.t)
: Tot (size_comp_for serialize_raw_data_item (Int64 ty x))

val size_comp_string
  (ty: major_type_byte_string_or_text_string)
  (x: U64.t)
  (v: Ghost.erased (Seq.seq byte) { Seq.length v == U64.v x /\ SZ.fits_u64 })
: Tot (size_comp_for serialize_raw_data_item (String ty (Ghost.reveal v)))

val l2r_write_uint64_header
  (ty: major_type_t { ty `U8.lt` major_type_simple_value })
  (x: U64.t)
: Tot (l2r_writer_for serialize_header (uint64_as_argument ty x))

val l2r_write_int64
  (ty: major_type_uint64_or_neg_int64)
  (x: U64.t)
: Tot (l2r_writer_for serialize_raw_data_item (Int64 ty x))

val maybe_r2l_write_int64
  (#opened: _)
  (m: major_type_uint64_or_neg_int64)
  (x: U64.t)
  (#vout: _)
  (out: W.t)
  (success: bool)
: STGhostT unit opened
   (maybe_r2l_write serialize_header out vout (uint64_as_argument m x) success)
   (fun _ -> maybe_r2l_write serialize_raw_data_item out vout (Int64 m x) success)

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val write_int64
  (m: major_type_uint64_or_neg_int64)
  (x: U64.t)
: Tot (maybe_r2l_writer_for serialize_raw_data_item (Int64 m x))

let finalize_raw_data_item_string_post_prop
  (m: major_type_byte_string_or_text_string)
  (va: v parse_raw_data_item_kind raw_data_item)
  (vp: AP.v byte)
: GTot prop
=
        FStar.UInt.fits (Seq.length (AP.contents_of vp)) U64.n /\
        va.contents == String m (AP.contents_of vp)

let finalize_raw_data_item_string_failure
  (m: major_type_byte_string_or_text_string)
  (vout: AP.array byte)
  (vp: AP.v byte)
: GTot prop
= 
  FStar.UInt.fits (Seq.length (AP.contents_of vp)) U64.n /\
  Seq.length (serialize serialize_raw_data_item (String m (AP.contents_of vp))) > AP.length vout + AP.length (AP.array_of vp)

[@@__reduce__]
let finalize_raw_data_item_string_post
  (m: major_type_byte_string_or_text_string)
  (vout: AP.array byte)
  (out: W.t)
  (vp: AP.v byte)
  (ap: byte_array)
  (res: bool)
: Tot vprop
=
      ifthenelse_vprop
        res
        (fun _ -> exists_ (fun vout' -> exists_ (fun a -> exists_ (fun va ->
          aparse parse_raw_data_item a va `star`
          W.vp out vout' `star`
          pure (
            AP.adjacent vout (AP.array_of vp) /\
            AP.merge_into vout' (array_of va) (AP.merge vout (AP.array_of vp)) /\
            finalize_raw_data_item_string_post_prop m va vp
        )))))
        (fun _ ->
          pure (finalize_raw_data_item_string_failure m vout vp) `star`
          W.vp out vout `star` AP.arrayptr ap vp
        )

val maybe_finalize_raw_data_item_string
  (#opened: _)
  (m: major_type_byte_string_or_text_string)
  (#vout: _)
  (out: W.t)
  (#vp: _)
  (ap: byte_array)
  (len: U64.t)
  (res: bool)
: STGhost unit opened
    (maybe_r2l_write serialize_header out vout (uint64_as_argument m len) res `star`
      AP.arrayptr ap vp
    )
    (fun _ ->
      finalize_raw_data_item_string_post m vout out vp ap res
    )
    (U64.v len == AP.length (AP.array_of vp) /\
      AP.adjacent vout (AP.array_of vp)
    )
    (fun _ -> True)

inline_for_extraction // necessary for the reexport into CBOR.SteelST
val finalize_raw_data_item_string
  (m: major_type_byte_string_or_text_string)
  (#vout: _)
  (out: W.t)
  (#vp: _)
  (ap: Ghost.erased byte_array)
  (len: U64.t)
: ST bool
    (W.vp out vout `star` AP.arrayptr ap vp)
    (fun res -> finalize_raw_data_item_string_post m vout out vp ap res)
    (U64.v len == AP.length (AP.array_of vp) /\
      AP.adjacent vout (AP.array_of vp)
    )
    (fun _ -> True)
