module CBOR.Spec.Raw.Valid
include CBOR.Spec.Raw.Base
open CBOR.Spec.Util
open FStar.Mul

module U8 = FStar.UInt8
module U64 = FStar.UInt64

noextract
let map_entry_order
  (#key: Type)
  (key_order: (key -> key -> bool))
  (value: Type)
  (m1: (key & value))
  (m2: (key & value))
: Tot bool
= key_order (fst m1) (fst m2)

noextract
let raw_data_item_sorted_elem (order: (raw_data_item -> raw_data_item -> bool)) (x: raw_data_item) : Tot bool
= match x with
  | Map _ l ->
      FStar.List.Tot.sorted (map_entry_order order _) l
  | _ -> true

noextract
let raw_data_item_sorted (order: (raw_data_item -> raw_data_item -> bool)) : Tot (raw_data_item -> bool)
= holds_on_raw_data_item (raw_data_item_sorted_elem order)

let raw_uint64_optimal (x: raw_uint64) : Tot bool =
  ((U64.v x.value <= U8.v max_simple_value_additional_info) = (x.size = 0)) &&
  begin
    if x.size <= 1
    then true
    else pow2 (8 * pow2 (x.size - 2)) <= U64.v x.value
  end

let raw_uint64_optimal_unique (x1 x2: raw_uint64) : Lemma
  (requires (raw_uint64_optimal x1 /\ raw_uint64_optimal x2 /\ raw_uint64_equiv x1 x2))
  (ensures (x1 == x2))
= ()

let rec raw_uint64_optimize (x: raw_uint64) : Pure raw_uint64
  (requires True)
  (ensures (fun x' -> raw_uint64_equiv x x' /\ raw_uint64_optimal x'))
  (decreases x.size)
= if U64.v x.value <= U8.v max_simple_value_additional_info
  then { x with size = 0 }
  else if x.size <= 1
  then x
  else if pow2 (8 * pow2 (x.size - 2)) <= U64.v x.value
  then x
  else raw_uint64_optimize { x with size = x.size - 1 }

let raw_data_item_ints_optimal_elem (x: raw_data_item) : Tot bool =
  match x with
  | Int64 _ v
  | String _ v _
  | Array v _
  | Map v _
  | Tagged v _
    -> raw_uint64_optimal v
  | Simple _ -> true

let raw_data_item_ints_optimal : raw_data_item -> Tot bool =
  holds_on_raw_data_item raw_data_item_ints_optimal_elem

let valid_raw_data_item_map
  (v: list (raw_data_item & raw_data_item))
: Tot bool
= list_no_setoid_repeats (map_entry_order raw_equiv _) v

let valid_raw_data_item_elem
  (l: raw_data_item)
: Tot bool
= match l with
  | Map _ v -> valid_raw_data_item_map v
  | _ -> true

let valid_raw_data_item
  (l: raw_data_item)
: Tot bool
= holds_on_raw_data_item valid_raw_data_item_elem l

let rec raw_equiv_sorted_optimal
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x1 x2: raw_data_item)
: Lemma
  (requires (
    raw_equiv x1 x2 /\
    raw_data_item_sorted order x1 /\
    raw_data_item_sorted order x2 /\
    raw_data_item_ints_optimal x1 /\
    raw_data_item_ints_optimal x2
  ))
  (ensures (x1 == x2))
  (decreases x1)
= raw_equiv_eq x1 x2;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x1;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x2;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x1;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x2;
  match x1, x2 with
  | Simple _, Simple _ -> ()
  | Int64 _ v1, Int64 _ v2 ->
    raw_uint64_optimal_unique v1 v2
  | String _ v1 _, String _ v2 _ ->
    raw_uint64_optimal_unique v1 v2
  | Tagged tag1 v1, Tagged tag2 v2 ->
    raw_uint64_optimal_unique tag1 tag2;
    raw_equiv_sorted_optimal order v1 v2
  | Array len1 l1, Array len2 l2 ->
    raw_uint64_optimal_unique len1 len2;
    assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
    list_for_all2_prod (raw_data_item_sorted order) (raw_data_item_sorted order) l1 l2;
    list_for_all2_prod raw_data_item_ints_optimal raw_data_item_ints_optimal l1 l2;
    list_for_all2_andp_intro
      (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
      (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal)
      l1 l2;
    list_for_all2_andp_intro
      (andp2
        (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
        (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal))
      raw_equiv
      l1 l2;
    list_for_all2_implies
      (andp2
        (andp2
          (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
          (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal))
        raw_equiv
      )
      ( = )
      l1 l2
      (fun x1' x2' ->
        raw_equiv_sorted_optimal order x1' x2'
      );
    list_for_all2_equals l1 l2
  | Map len1 l1, Map len2 l2 ->
    raw_uint64_optimal_unique len1 len2;
    assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
    list_for_all_andp (holds_on_pair (raw_data_item_sorted order)) (holds_on_pair raw_data_item_ints_optimal) l1;
    list_for_all_andp (holds_on_pair (raw_data_item_sorted order)) (holds_on_pair raw_data_item_ints_optimal) l2;
    list_for_all_exists_prodp
      (holds_on_pair2 raw_equiv)
      (andp
        (holds_on_pair (raw_data_item_sorted order))
        (holds_on_pair raw_data_item_ints_optimal)
      )
      (andp
        (holds_on_pair (raw_data_item_sorted order))
        (holds_on_pair raw_data_item_ints_optimal)
      )
      l1 l2;
    list_for_all_exists_implies
      (andp2
        (holds_on_pair2 raw_equiv)
        (prodp
          (andp
            (holds_on_pair (raw_data_item_sorted order))
            (holds_on_pair raw_data_item_ints_optimal)
          )
          (andp
            (holds_on_pair (raw_data_item_sorted order))
            (holds_on_pair raw_data_item_ints_optimal)
          )
        )
      )
      ( = )
      l1 l2
      (fun x1 x2 ->
        raw_equiv_sorted_optimal order (fst x1) (fst x2);
        raw_equiv_sorted_optimal order (snd x1) (snd x2)
      );
    list_for_all_exists_equal_eq l1 l2;
    list_for_all_exists_prodp
      (holds_on_pair2 raw_equiv)
      (andp
        (holds_on_pair (raw_data_item_sorted order))
        (holds_on_pair raw_data_item_ints_optimal)
      )
      (andp
        (holds_on_pair (raw_data_item_sorted order))
        (holds_on_pair raw_data_item_ints_optimal)
      )
      l2 l1;
    list_for_all_exists_implies
      (andp2
        (holds_on_pair2 raw_equiv)
        (prodp
          (andp
            (holds_on_pair (raw_data_item_sorted order))
            (holds_on_pair raw_data_item_ints_optimal)
          )
          (andp
            (holds_on_pair (raw_data_item_sorted order))
            (holds_on_pair raw_data_item_ints_optimal)
          )
        )
      )
      ( = )
      l2 l1
      (fun x2 x1 ->
        raw_equiv_sym (fst x2) (fst x1);
        raw_equiv_sorted_optimal order (fst x1) (fst x2);
        raw_equiv_sym (snd x2) (snd x1);
        raw_equiv_sorted_optimal order (snd x1) (snd x2)
      );
    list_for_all_exists_equal_eq l2 l1;
    list_sorted_ext_eq (map_entry_order order _) l1 l2

let rec raw_data_item_sorted_optimal_valid_aux
  (order: (raw_data_item -> raw_data_item -> bool) {
    order_irrefl order /\
    order_trans order
  })
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) l /\
    List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) l /\
    FStar.List.Tot.sorted (map_entry_order order _) l
  ))
  (ensures (
    list_no_setoid_repeats (map_entry_order raw_equiv _) l
  ))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    raw_data_item_sorted_optimal_valid_aux order q;
    if List.Tot.existsb (map_entry_order raw_equiv _ a) q
    then begin
      let a' = list_existsb_elim (map_entry_order raw_equiv _ a) q in
      list_sorted_memP (map_entry_order order _) a q a';
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) q;
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_ints_optimal)) q;
      raw_equiv_sorted_optimal order (fst a) (fst a')
    end
    else ()

let raw_data_item_sorted_optimal_valid
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x1: raw_data_item)
: Lemma
  (requires (
    raw_data_item_sorted order x1 /\
    raw_data_item_ints_optimal x1
  ))
  (ensures (valid_raw_data_item x1))
= holds_on_raw_data_item_andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem x1;
  holds_on_raw_data_item_implies
    (andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem)
    valid_raw_data_item_elem
    (fun x ->
      match x with
      | Map len v ->
        holds_on_raw_data_item_andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem x;
          holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) (Map len v);
          holds_on_raw_data_item_eq (raw_data_item_ints_optimal_elem) (Map len v);
          assert (List.Tot.for_all (holds_on_pair (holds_on_raw_data_item raw_data_item_ints_optimal_elem)) v);
          assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
          assert (List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) v);
          raw_data_item_sorted_optimal_valid_aux order v
      | _ -> ()
    )
    x1
