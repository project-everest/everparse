module CBOR.Spec.Raw.Valid2
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

let basic_data_model (x1 x2: raw_data_item) : Tot bool = false

unfold let raw_equiv2 = equiv basic_data_model
