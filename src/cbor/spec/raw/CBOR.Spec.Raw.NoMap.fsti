module CBOR.Spec.Raw.NoMap
include CBOR.Spec.Raw.Valid
open CBOR.Spec.Util
open FStar.Mul

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* When there are no maps in map keys, equivalence and absence of
   setoid duplicates can be checked in constant stack space. *)

(*
let rec raw_equiv_list_no_map
  (l1 l2: list raw_data_item)
: Tot bool
  (decreases (list_sum raw_data_item_size l1))
= match l1, l2 with
  | [], [] -> true
  | x1 :: q1, x2 :: q2 ->
    raw_data_item_size_eq x1;
    begin match x1, x2 with
    | Simple v1, Simple v2 -> v1 = v2 && raw_equiv_list_no_map q1 q2
    | Int64 ty1 v1, Int64 ty2 v2 -> ty1 = ty2 && raw_uint64_equiv v1 v2 && raw_equiv_list_no_map q1 q2
    | String ty1 len1 v1, String ty2 len2 v2 -> ty1 = ty2 && raw_uint64_equiv len1 len2 && v1 = v2 && raw_equiv_list_no_map q1 q2
    | Array len1 v1, Array len2 v2 ->
      list_sum_append raw_data_item_size v1 q1;
      raw_uint64_equiv len1 len2 &&
      raw_equiv_list_no_map (List.Tot.append v1 q1) (List.Tot.append v2 q2)
    | Tagged tag1 v1, Tagged tag2 v2 ->
      raw_uint64_equiv tag1 tag2 &&
      raw_equiv_list_no_map (v1 :: q1) (v2 :: q2)
    | _ -> false
    end
  | _ -> false

val raw_equiv_list_no_map_append
  (ll1 lr1 ll2 lr2: list raw_data_item)
: Lemma
  (requires (List.Tot.length ll1 == List.Tot.length ll2))
  (ensures (raw_equiv_list_no_map (List.Tot.append ll1 lr1) (List.Tot.append ll2 lr2) == (raw_equiv_list_no_map ll1 ll2 && raw_equiv_list_no_map lr1 lr2)))

val raw_equiv_list_no_map_no_map
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (List.Tot.for_all (holds_on_raw_data_item (notp Map?)) l1 == true))

val raw_equiv_list_no_map_equiv
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (list_for_all2 raw_equiv l1 l2 == true))

val raw_equiv_list_no_map_sym
  (l1 l2: list raw_data_item)
: Lemma
  (raw_equiv_list_no_map l1 l2 == raw_equiv_list_no_map l2 l1)

val raw_equiv_equiv_list_no_map
  (l1 l2: list raw_data_item)
: Lemma
  (requires (
    list_for_all2 raw_equiv l1 l2 == true /\
    list_for_all2 (prod_or (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?))) l1 l2 == true
  ))
  (ensures (
    raw_equiv_list_no_map l1 l2 == true
  ))

val raw_equiv_list_no_map_eq
  (l1 l2: list raw_data_item)
: Lemma
  (raw_equiv_list_no_map l1 l2 == (list_for_all2 raw_equiv l1 l2 && list_for_all2 (prod_or (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?))) l1 l2))

let raw_equiv_no_map
  (x1 x2: raw_data_item)
: Tot bool
= raw_equiv_list_no_map [x1] [x2]

let raw_equiv_list_no_map_no_map2
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (List.Tot.for_all (holds_on_raw_data_item (notp Map?)) l1 == true /\
    List.Tot.for_all (holds_on_raw_data_item (notp Map?)) l2 == true
  ))
= raw_equiv_list_no_map_no_map l1 l2;
  raw_equiv_list_no_map_sym l1 l2;
  raw_equiv_list_no_map_no_map l2 l1

val raw_equiv_list_no_map_eq'
  (l1 l2: list raw_data_item)
: Lemma
  (ensures (raw_equiv_list_no_map l1 l2 == list_for_all2 raw_equiv_no_map l1 l2))

let no_maps_in_keys_map
  (v: list (raw_data_item & raw_data_item))
: Tot bool
= List.Tot.for_all (holds_on_raw_data_item (notp Map?)) (List.Tot.map fst v)

let no_maps_in_keys_elem
  (l: raw_data_item)
: Tot bool
= match l with
  | Map _ v -> no_maps_in_keys_map v
  | _ -> true

let no_maps_in_keys = holds_on_raw_data_item no_maps_in_keys_elem


let valid_raw_data_item_no_maps_in_keys_map
  (v: list (raw_data_item & raw_data_item))
: Tot bool
= list_no_setoid_repeats (map_entry_order raw_equiv_no_map _) v

let valid_raw_data_item_no_maps_in_keys_elem_gen
  (p: raw_data_item -> bool)
  (l: raw_data_item)
: Tot bool
= p l &&
  begin match l with
  | Map _ v -> valid_raw_data_item_no_maps_in_keys_map v
  | _ -> true
  end

let valid_raw_data_item_no_maps_in_keys_elem =
  valid_raw_data_item_no_maps_in_keys_elem_gen no_maps_in_keys_elem

let valid_raw_data_item_no_maps_in_keys_gen
  (p: raw_data_item -> bool)
: Tot (raw_data_item -> bool)
= holds_on_raw_data_item (valid_raw_data_item_no_maps_in_keys_elem_gen p)

let valid_raw_data_item_no_maps_in_keys = holds_on_raw_data_item valid_raw_data_item_no_maps_in_keys_elem

val valid_no_maps_in_keys_no_maps_in_keys_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item_no_maps_in_keys_gen p x == true))
  (ensures (holds_on_raw_data_item p x == true))

let valid_no_maps_in_keys_no_maps_in_keys
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item_no_maps_in_keys x == true))
  (ensures (no_maps_in_keys x == true))
= assert_norm (valid_raw_data_item_no_maps_in_keys == valid_raw_data_item_no_maps_in_keys_gen no_maps_in_keys_elem);
  valid_no_maps_in_keys_no_maps_in_keys_gen no_maps_in_keys_elem x

val valid_no_maps_in_keys_valid_map
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair valid_raw_data_item_no_maps_in_keys) l == true /\
    no_maps_in_keys_map l == true /\
    valid_raw_data_item_no_maps_in_keys_map l == true
  ))
  (ensures (
    valid_raw_data_item_map l == true
  ))

val valid_no_maps_in_keys_valid
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item_no_maps_in_keys x == true))
  (ensures (valid_raw_data_item x == true))

val valid_no_maps_in_keys_valid_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (
    valid_raw_data_item_no_maps_in_keys_gen p x == true /\
    (forall x' . p x' == true ==> no_maps_in_keys_elem x' == true)
  ))
  (ensures (valid_raw_data_item x == true))

val valid_valid_no_maps_in_keys_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item x == true /\
    holds_on_raw_data_item p x == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys_gen p x == true))

val valid_valid_no_maps_in_keys
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item x == true /\
    no_maps_in_keys x == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys x == true))

val valid_raw_data_item_no_maps_in_keys_eq
  (x: raw_data_item)
: Lemma
  (valid_raw_data_item_no_maps_in_keys x ==
    (valid_raw_data_item x && no_maps_in_keys x)
  )

val valid_raw_data_item_no_maps_in_keys_gen_eq
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (
    forall x' . p x' == true ==> no_maps_in_keys_elem x' == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys_gen p x ==
    (valid_raw_data_item x && holds_on_raw_data_item p x)
  ))

