module CBOR.Spec.Raw.Sort
open CBOR.Spec.Raw.Map

let cbor_map_sort = map_sort cbor_compare

let cbor_map_sort_eq
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (cbor_map_sort l == map_sort cbor_compare l)
= ()

let cbor_map_sort_correct x =
  cbor_map_sort_eq x;
  Classical.forall_intro_2 deterministically_encoded_cbor_map_key_order_spec;
  Classical.forall_intro_2 cbor_compare_correct;
  Classical.forall_intro_2 cbor_compare_equal;
  Classical.forall_intro_2 bytes_lex_compare_opp;
  Classical.forall_intro_2 (list_ghost_assoc_eq #raw_data_item #raw_data_item);
  map_sort_correct deterministically_encoded_cbor_map_key_order cbor_compare x
