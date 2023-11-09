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

let deterministically_encoded_cbor_map_key_order = CBOR.Spec.Format.deterministically_encoded_cbor_map_key_order

let deterministically_encoded_cbor_map_key_order_irrefl
  x
= Classical.move_requires (CBOR.Spec.Format.deterministically_encoded_cbor_map_key_order_irrefl x) x

let deterministically_encoded_cbor_map_key_order_trans
  x y z
= CBOR.Spec.Format.deterministically_encoded_cbor_map_key_order_trans x y z

let rec list_ghost_assoc_eq
  (#key #value: Type)
  (k: key)
  (m: list (key & value))
: Lemma
  (list_ghost_assoc k m == LowParse.Spec.Assoc.list_ghost_assoc k m)
  [SMTPat (list_ghost_assoc k m)]
= match m with
  | [] -> ()
  | (k', _) :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then ()
    else list_ghost_assoc_eq k m'

let deterministically_encoded_cbor_map_key_order_assoc_ext
  m1 m2 ext
= CBOR.Spec.Format.deterministically_encoded_cbor_map_key_order_assoc_ext m1 m2 ext

let deterministically_encoded_cbor_map_key_order_major_type_intro
  v1 v2
= CBOR.Spec.Format.deterministically_encoded_cbor_map_key_order_major_type_intro v1 v2

let deterministically_encoded_cbor_map_key_order_int64
  ty v1 v2
= CBOR.Spec.Format.lex_order_int64_correct ty v1 v2
