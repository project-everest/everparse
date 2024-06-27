module CBOR.Spec.Raw.Sort
include CBOR.Spec.Raw.Order
open CBOR.Spec.Util

noextract [@@noextract_to "krml"]
val cbor_map_sort
  (l: list (raw_data_item & raw_data_item))
: Tot (bool & list (raw_data_item & raw_data_item))

val cbor_map_sort_correct
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (ensures (let (res, l') = cbor_map_sort l in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l') <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (res == true <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (res == true ==> (
      List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l' /\
      (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
    ))
  ))
  [SMTPat (cbor_map_sort l)]

let cbor_map_sort_failsafe
  (l: list (raw_data_item & raw_data_item))
: Tot (list (raw_data_item & raw_data_item))
= snd (cbor_map_sort l)

let cbor_map_sort_failsafe_correct
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (let l' = cbor_map_sort_failsafe l in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l) ==> (
      List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) l' /\
      List.Tot.no_repeats_p (List.Tot.map fst l')      
    ))
  )
= ()

let cbor_raw_sort_elem
  (x: raw_data_item)
: Tot raw_data_item
= match x with
  | Map len v -> Map len (cbor_map_sort_failsafe v)
  | _ -> x

let cbor_raw_sort_elem_ints_optimal
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true))
  (ensures (raw_data_item_ints_optimal (cbor_raw_sort_elem x) == true))
= assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem (cbor_raw_sort_elem x);
  match x with
  | Map len v ->
    list_for_all_intro (holds_on_pair raw_data_item_ints_optimal) (cbor_map_sort_failsafe v) (fun x ->
      List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v
    )
  | _ -> ()

let cbor_raw_sort_elem_equiv
  (x: raw_data_item)
: Lemma
  (ensures (raw_equiv x (cbor_raw_sort_elem x) == true))
= raw_equiv_eq x (cbor_raw_sort_elem x);
  match x with
  | Map len v ->
    list_for_all_intro (list_existsb2 (holds_on_pair2 raw_equiv) (cbor_map_sort_failsafe v)) v (fun _ -> assume False);
    list_for_all_intro (list_existsb2 (holds_on_pair2 raw_equiv) v) (cbor_map_sort_failsafe v) (fun _ -> assume False)    
  | _ -> raw_equiv_refl x

let cbor_raw_sort = raw_data_item_fmap cbor_raw_sort_elem
