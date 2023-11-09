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
val dummy_cbor : cbor

inline_for_extraction
noextract
val cbor_map_entry_key: cbor_map_entry -> cbor

inline_for_extraction
noextract
val cbor_map_entry_value: cbor_map_entry -> cbor

val cbor_map_entry_key_value_inj
  (m1 m2: cbor_map_entry)
: Lemma
  (requires (
    cbor_map_entry_key m1 == cbor_map_entry_key m2 /\
    cbor_map_entry_value m1 == cbor_map_entry_value m2
  ))
  (ensures (m1 == m2))
  [SMTPatOr [
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_value m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_value m2)];
  ]]

inline_for_extraction
noextract
val mk_cbor_map_entry
  (key: cbor)
  (value: cbor)
: Pure cbor_map_entry
  (requires True)
  (ensures (fun res ->
    cbor_map_entry_key res == key /\
    cbor_map_entry_value res == value
  ))

inline_for_extraction
noextract
val cbor_array_iterator_t: Type0

inline_for_extraction
noextract
val cbor_map_iterator_t: Type0
