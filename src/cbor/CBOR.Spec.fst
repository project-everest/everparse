module CBOR.Spec
open CBOR.Spec.Format
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch

let serialize_cbor
  c
= LPS.serialize serialize_raw_data_item c

let serialize_cbor_inj
  c1 c2 s1 s2
= LPS.parse_strong_prefix parse_raw_data_item (serialize_cbor c1) (serialize_cbor c1 `Seq.append` s1);
  LPS.parse_strong_prefix parse_raw_data_item (serialize_cbor c2) (serialize_cbor c2 `Seq.append` s2);
  LPS.serializer_injective _ serialize_raw_data_item c1 c2;
  Seq.lemma_append_inj (serialize_cbor c1) s1 (serialize_cbor c2) s2

let serialize_cbor_nonempty
  c
= ()
