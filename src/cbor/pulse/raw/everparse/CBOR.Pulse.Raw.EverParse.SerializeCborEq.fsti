module CBOR.Pulse.Raw.EverParse.SerializeCborEq

(* Tiny helper exposing that `serialize_cbor v` (which is opaque since
   `serialize_cbor` is declared with `val` in `CBOR.Spec.Raw.Format.fsti`)
   equals the EverParse-level `bare_serialize serialize_raw_data_item v`. *)

module LP = LowParse.Spec.Base
module LPC = LowParse.Spec.Combinators

open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse

val serialize_cbor_eq_bare_serialize
  (v: raw_data_item)
: Lemma (serialize_cbor v == LP.bare_serialize serialize_raw_data_item v)

(* Pair-level byte-compare correctness, in `Format.bytes_lex_compare`
   terms. Bridges:
   1. `serialize_nondep_then_eq`  : bare_serialize pair_ser kv == bare_serialize s (fst kv) ++ bare_serialize s (snd kv)
   2. `bytes_lex_compare_serialize_strong_prefix` : bytes_lex_compare on
      appends decomposes when the first part is a `ParserStrong` serializer
   3. `cbor_compare_correct` + `serialize_cbor_eq_bare_serialize` : connect
      `cbor_compare` to `Format.bytes_lex_compare` of `bare_serialize`. *)
val pair_byte_compare_eq_cbor_compare_pair
  (kv1 kv2: raw_data_item & raw_data_item)
: Lemma
  (let pair_ser = LPC.serialize_nondep_then serialize_raw_data_item serialize_raw_data_item in
   bytes_lex_compare (LP.bare_serialize pair_ser kv1) (LP.bare_serialize pair_ser kv2) == (
     let c = cbor_compare (fst kv1) (fst kv2) in
     if c = 0 then cbor_compare (snd kv1) (snd kv2) else c
   ))

