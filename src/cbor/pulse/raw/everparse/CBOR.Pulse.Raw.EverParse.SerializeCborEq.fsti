module CBOR.Pulse.Raw.EverParse.SerializeCborEq

(* Tiny helper exposing that `serialize_cbor v` (which is opaque since
   `serialize_cbor` is declared with `val` in `CBOR.Spec.Raw.Format.fsti`)
   equals the EverParse-level `bare_serialize serialize_raw_data_item v`. *)

module LP = LowParse.Spec.Base

open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse

val serialize_cbor_eq_bare_serialize
  (v: raw_data_item)
: Lemma (serialize_cbor v == LP.bare_serialize serialize_raw_data_item v)
