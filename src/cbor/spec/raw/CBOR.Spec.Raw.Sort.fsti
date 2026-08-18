module CBOR.Spec.Raw.Sort
include CBOR.Spec.Raw.Optimal
open CBOR.Spec.Util

let compare_prop
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int)
: Tot prop
=
    (forall x . order x x == false) /\
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . compare x y == 0 <==> x == y) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0))

noextract [@@noextract_to "krml"]
val cbor_map_sort
  (order: raw_data_item -> raw_data_item -> bool)
  (l: list (raw_data_item & raw_data_item))
: Tot (list (raw_data_item & raw_data_item))

val cbor_map_sort_correct
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    compare_prop order compare
  })
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires List.Tot.no_repeats_p (List.Tot.map fst l))
  (ensures (let l' = cbor_map_sort order l in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l')) /\
    List.Tot.sorted (map_entry_order order _) l' /\
    (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
  ))

let cbor_map_sort_failsafe
  (order: raw_data_item -> raw_data_item -> bool)
  (l: list (raw_data_item & raw_data_item))
: Tot (list (raw_data_item & raw_data_item))
= if List.Tot.noRepeats (List.Tot.map fst l)
  then cbor_map_sort order l
  else l

let cbor_map_sort_failsafe_correct
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    compare_prop order compare
  })
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (let l' = cbor_map_sort_failsafe order l in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l') <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l) ==> (
      List.Tot.sorted (map_entry_order order _) l' /\
      List.Tot.no_repeats_p (List.Tot.map fst l') /\
      (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
    ))
  )
= Classical.move_requires (cbor_map_sort_correct order compare) l

let cbor_raw_sort_elem
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    compare_prop order compare
  })
  (x: raw_data_item)
: Tot raw_data_item
= Classical.forall_intro (cbor_map_sort_failsafe_correct order compare);
  match x with
  | Map len v -> Map len (cbor_map_sort_failsafe order v)
  | _ -> x

let cbor_raw_sort order compare = raw_data_item_fmap (cbor_raw_sort_elem order compare)

val cbor_raw_sort_correct
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    compare_prop order compare
  })
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true /\
    valid_raw_data_item x == true
  ))
  (ensures (
    let x' = cbor_raw_sort order compare x in
    raw_data_item_ints_optimal x' == true /\
    raw_data_item_sorted order x' == true /\
    valid_raw_data_item x'  == true /\
    raw_equiv x x' /\
    begin match x, x' with
    | Map len _, Map len' _ -> len.value == len'.value
    | Map _ _, _ | _, Map _ _ -> False
    | _ -> True
    end
  ))

let cbor_raw_sort_equiv = cbor_raw_sort_correct
