module CBOR.Spec.Raw.Sort
include CBOR.Spec.Raw.Optimal
include CBOR.Spec.Raw.Format
open CBOR.Spec.Util

noextract [@@noextract_to "krml"]
val cbor_map_sort
  (l: list (raw_data_item & raw_data_item))
: Tot (list (raw_data_item & raw_data_item))

val cbor_map_sort_correct
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires List.Tot.no_repeats_p (List.Tot.map fst l))
  (ensures (let l' = cbor_map_sort l in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l')) /\
    List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l' /\
    (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
  ))
  [SMTPat (cbor_map_sort l)]

let cbor_map_sort_failsafe
  (l: list (raw_data_item & raw_data_item))
: Tot (list (raw_data_item & raw_data_item))
= if List.Tot.noRepeats (List.Tot.map fst l)
  then cbor_map_sort l
  else l

let cbor_map_sort_failsafe_correct
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (let l' = cbor_map_sort_failsafe l in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l') <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l) ==> (
      List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l' /\
      List.Tot.no_repeats_p (List.Tot.map fst l') /\
      (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
    ))
  )
= ()

let cbor_raw_sort_elem
  (x: raw_data_item)
: Tot raw_data_item
= match x with
  | Map len v -> Map len (cbor_map_sort_failsafe v)
  | _ -> x

let cbor_raw_sort = raw_data_item_fmap cbor_raw_sort_elem

val cbor_raw_sort_correct
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true /\
    valid_raw_data_item x == true
  ))
  (ensures (
    let x' = cbor_raw_sort x in
    raw_data_item_ints_optimal x' == true /\
    raw_data_item_sorted deterministically_encoded_cbor_map_key_order x' == true /\
    valid_raw_data_item x'  == true /\
    raw_equiv x x' /\
    begin match x, x' with
    | Map len _, Map len' _ -> len.value == len'.value
    | Map _ _, _ | _, Map _ _ -> False
    | _ -> True
    end
  ))

let cbor_raw_sort_equiv = cbor_raw_sort_correct
