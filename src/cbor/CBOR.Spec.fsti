module CBOR.Spec
include CBOR.Spec.Type

module U8 = FStar.UInt8

(* Data format specification *)

val serialize_cbor
  (c: raw_data_item)
: GTot (Seq.seq U8.t)

val serialize_cbor_inj
  (c1 c2: raw_data_item)
  (s1 s2: Seq.seq U8.t)
: Lemma
  (requires (serialize_cbor c1 `Seq.append` s1 == serialize_cbor c2 `Seq.append` s2))
  (ensures (c1 == c2 /\ s1 == s2))

val serialize_cbor_nonempty
  (c: raw_data_item)
: Lemma
  (Seq.length (serialize_cbor c) > 0)
