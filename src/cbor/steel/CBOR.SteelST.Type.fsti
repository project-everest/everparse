module CBOR.SteelST.Type
include CBOR.SteelST.Type.Base
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

(* The C datatype for CBOR objects *)

inline_for_extraction
noextract
val cbor_map_entry: Type0

inline_for_extraction
noextract
val cbor: Type0

inline_for_extraction
noextract
val cbor_array_iterator_t: Type0

inline_for_extraction
noextract
val cbor_map_iterator_t: Type0
