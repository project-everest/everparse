module CBOR.Spec.Raw.Valid
include CBOR.Spec.Raw.Base
open CBOR.Spec.Util

val valid
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool

val equiv
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x1 x2: raw_data_item)
: Tot bool

val valid_eq
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (ensures (valid data_model x == (
    match x with
    | Array _ v -> List.Tot.for_all (valid data_model) v
    | Tagged _ v -> valid data_model v
    | Map _ v ->
      List.Tot.for_all (valid data_model) (List.Tot.map fst v) &&
      List.Tot.for_all (valid data_model) (List.Tot.map snd v) &&
      list_no_setoid_repeats (equiv data_model) (List.Tot.map fst v)
    | _ -> true
  )))

val equiv_eq
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x1 x2: raw_data_item)
: Lemma
  (ensures equiv data_model x1 x2 == (
  if data_model x1 x2
  then true
  else if x1 = x2
  then true
  else
    valid data_model x1 && valid data_model x2 &&
    begin match x1, x2 with
    | Array _ v1, Array _ v2 ->
      list_for_all2 (equiv data_model) v1 v2
    | Map _ v1, Map _ v2 ->
      List.Tot.for_all (setoid_assoc_eq (equiv data_model) (equiv data_model) v2) v1 &&
      List.Tot.for_all (setoid_assoc_eq (equiv data_model) (equiv data_model) v1) v2
    | Tagged tag1 v1, Tagged tag2 v2 ->
      tag1.value = tag2.value &&
      equiv data_model v1 v2
    | Int64 ty1 v1, Int64 ty2 v2 ->
      ty1 = ty2 && v1.value = v2.value
    | String ty1 _ v1, String ty2 _ v2 ->
      ty1 = ty2 && v1 = v2
    | _ -> false
    end
  ))

val equiv_refl
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x1: raw_data_item)
: Lemma
  (ensures equiv data_model x1 x1)

let equiv_refl_forall
  (data_model: (raw_data_item -> raw_data_item -> bool))
: Lemma
  (ensures forall x1 . equiv data_model x1 x1)
= Classical.forall_intro (equiv_refl data_model)

val equiv_sym
  (data_model: (raw_data_item -> raw_data_item -> bool) {
    forall x1 x2 . data_model x1 x2 == data_model x2 x1
  })
  (x1 x2: raw_data_item)
: Lemma
  (ensures equiv data_model x1 x2 == equiv data_model x2 x1)

let equiv_sym_forall
  (data_model: (raw_data_item -> raw_data_item -> bool) {
    forall x1 x2 . data_model x1 x2 == data_model x2 x1
  })
: Lemma
  (ensures forall x1 x2 . equiv data_model x1 x2 == equiv data_model x2 x1)
= Classical.forall_intro_2 (equiv_sym data_model)

val equiv_trans
  (data_model: (raw_data_item -> raw_data_item -> bool) {
    (forall x1 x2 . data_model x1 x2 == data_model x2 x1) /\
    (forall x1 x2 x3 . (data_model x1 x2 /\ equiv data_model x2 x3) ==> data_model x1 x3)
  })
  (x1 x2 x3: raw_data_item)
: Lemma
  (requires (equiv data_model x1 x2 /\ equiv data_model x2 x3))
  (ensures (equiv data_model x1 x3))

let equiv_trans_forall
  (data_model: (raw_data_item -> raw_data_item -> bool) {
    (forall x1 x2 . data_model x1 x2 == data_model x2 x1) /\
    (forall x1 x2 x3 . (data_model x1 x2 /\ equiv data_model x2 x3) ==> data_model x1 x3)
  })
: Lemma
  (forall x1 x2 x3 .  (equiv data_model x1 x2 /\ equiv data_model x2 x3) ==> equiv data_model x1 x3)
= let prf
    x1 x2 x3
  : Lemma ((equiv data_model x1 x2 /\ equiv data_model x2 x3) ==> equiv data_model x1 x3)
  = Classical.move_requires (equiv_trans data_model x1 x2) x3
  in
  Classical.forall_intro_3 prf

let valid_item
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
=   match x with
    | Map _ v ->
      (list_no_setoid_repeats (equiv data_model) (List.Tot.map fst v))
    | _ -> true

val valid_eq'
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (ensures (valid data_model x == holds_on_raw_data_item (valid_item data_model) x))

let valid_map
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (v: list (raw_data_item & raw_data_item))
: Tot bool
= list_no_setoid_repeats (equiv data_model) (List.Tot.map fst v)

noextract
let map_entry_order
  (#key: Type)
  (key_order: (key -> key -> bool))
  (value: Type)
  (m1: (key & value))
  (m2: (key & value))
: Tot bool
= key_order (fst m1) (fst m2)

let valid_map'
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (v: list (raw_data_item & raw_data_item))
: Tot bool
= list_no_setoid_repeats (map_entry_order (equiv data_model) _) v

let rec list_existsb_map_fst
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (a: (raw_data_item & raw_data_item))
  (v: list (raw_data_item & raw_data_item))
: Lemma
  (ensures List.Tot.existsb (map_entry_order (equiv data_model) _ a) v == List.Tot.existsb (equiv data_model (fst a)) (List.Tot.map fst v))
  (decreases v)
= match v with
  | [] -> ()
  | (a', _) :: q ->
    if equiv data_model (fst a) a'
    then ()
    else list_existsb_map_fst data_model a q

let rec valid_map_eq
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (v: list (raw_data_item & raw_data_item))
: Lemma
  (valid_map data_model v == valid_map' data_model v)
= match v with
  | [] -> ()
  | kv :: v' ->
    valid_map_eq data_model v';
    list_existsb_map_fst data_model kv v';
    ()

let basic_data_model (x1 x2: raw_data_item) : Tot bool = false

unfold let raw_equiv2 = equiv basic_data_model
unfold let raw_equiv = raw_equiv2
unfold let valid_raw_data_item = valid basic_data_model
unfold let valid_raw_data_item_elem = valid_item basic_data_model
unfold let raw_equiv_refl = equiv_refl basic_data_model
unfold let raw_equiv_sym = equiv_sym basic_data_model
unfold let raw_equiv_trans = equiv_trans basic_data_model

let valid_raw_data_item_map_fmap_equiv
  (data_model: (raw_data_item -> raw_data_item -> bool) {
    (forall x1 x2 . data_model x1 x2 == data_model x2 x1) /\
    (forall x1 x2 x3 . (data_model x1 x2 /\ equiv data_model x2 x3) ==> data_model x1 x3)
  })
  (f: raw_data_item -> raw_data_item)
  (l: list (raw_data_item & raw_data_item))
  (prf: (x: raw_data_item { (List.Tot.memP x (List.Tot.map fst l)) /\ x << l }) -> Lemma
    (requires (valid data_model x))
    (ensures (equiv data_model x (f x) == true))
  )
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair (holds_on_raw_data_item (valid_item data_model))) l /\
    valid_map data_model l == true
  ))
  (ensures (valid_map data_model (List.Tot.map (apply_on_pair f) l) == true))
= 
  valid_map_eq data_model l;
        list_no_setoid_repeats_map (apply_on_pair f) l (map_entry_order (equiv data_model) _) (map_entry_order (equiv data_model) _) (fun x x' ->
          List.Tot.for_all_mem (holds_on_pair (holds_on_raw_data_item (valid_item data_model))) l;
          valid_eq' data_model (fst x);
          valid_eq' data_model (fst x');
          List.Tot.memP_map_intro fst x l;
          prf (fst x);
          List.Tot.memP_map_intro fst x' l;
          prf (fst x');
          equiv_sym data_model (f (fst x')) (fst x');
          equiv_trans data_model (fst x) (f (fst x)) (f (fst x'));
          equiv_trans data_model (fst x) (f (fst x')) (fst x')
        );
  valid_map_eq data_model (List.Tot.map (apply_on_pair f) l)

let raw_equiv'
  (x1 x2: raw_data_item)
: Tot bool
=
    valid basic_data_model x1 && valid basic_data_model x2 &&
    begin match x1, x2 with
    | Array _ v1, Array _ v2 ->
      list_for_all2 (equiv basic_data_model) v1 v2
    | Map _ v1, Map _ v2 ->
      List.Tot.for_all (setoid_assoc_eq (equiv basic_data_model) (equiv basic_data_model) v2) v1 &&
      List.Tot.for_all (setoid_assoc_eq (equiv basic_data_model) (equiv basic_data_model) v1) v2
    | Tagged tag1 v1, Tagged tag2 v2 ->
      tag1.value = tag2.value &&
      equiv basic_data_model v1 v2
    | Int64 ty1 v1, Int64 ty2 v2 ->
      ty1 = ty2 && v1.value = v2.value
    | String ty1 _ v1, String ty2 _ v2 ->
      ty1 = ty2 && v1 = v2
    | Simple v1, Simple v2 -> v1 = v2
    | _ -> false
    end

let raw_equiv'_refl_valid
  (x: raw_data_item)
: Lemma
  (requires (valid basic_data_model x))
  (ensures (raw_equiv' x x))
= valid_eq basic_data_model x;
  equiv_refl_forall basic_data_model;
  equiv_sym_forall basic_data_model;
  equiv_trans_forall basic_data_model;
  match x with
  | Array len v ->
    List.Tot.for_all_mem (valid basic_data_model) v;
    list_for_all2_refl raw_equiv v (fun x -> ())
  | Map len v -> list_setoid_assoc_eq_refl raw_equiv raw_equiv v
  | _ -> ()

let raw_equiv_eq_valid
  (x1 x2: raw_data_item)
: Lemma
  (requires (valid_raw_data_item x1 /\
    valid_raw_data_item x2
  ))
  (ensures (raw_equiv x1 x2 == raw_equiv' x1 x2))
= equiv_eq basic_data_model x1 x2;
  if x1 = x2
  then raw_equiv'_refl_valid x1
  else ()
