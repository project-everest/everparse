module CBOR.Spec.Raw.Sort
include CBOR.Spec.Raw.Order

noextract [@@noextract_to "krml"]
val cbor_map_sort
  (l: list (raw_data_item & raw_data_item))
: Tot (bool & list (raw_data_item & raw_data_item))

val cbor_map_sort_correct
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (ensures (let (res, l') = cbor_map_sort l in
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l') <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (res == true <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (res == true ==> (
      List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l' /\
      (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
    ))
  ))
  [SMTPat (cbor_map_sort l)]

