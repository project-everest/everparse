module CBOR.Spec.Raw.Valid

let raw_data_item_size_eq_pat
  (x: raw_data_item)
: Lemma
  (ensures (raw_data_item_size x == begin match x with
  | Array _ v -> 2 + list_sum raw_data_item_size v
  | Map _ v -> 2 + list_sum (pair_sum raw_data_item_size raw_data_item_size) v
  | Tagged _ v -> 2 + raw_data_item_size v
  | _ -> 1
  end))
  [SMTPat (raw_data_item_size x)]
= raw_data_item_size_eq x

let rec valid'
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (fuel: nat)
: Tot (raw_data_item -> bool)
  (decreases fuel)
= fun x ->
  if raw_data_item_size x > fuel
  then false
  else match x with
  | Array _ v -> List.Tot.for_all (valid' data_model (fuel - 1)) v
  | Tagged _ v -> valid' data_model (fuel - 1) v
  | Map _ v ->
    List.Tot.for_all (valid' data_model (fuel - 1)) (List.Tot.map fst v) &&
    List.Tot.for_all (valid' data_model (fuel - 1)) (List.Tot.map snd v) &&
    (list_no_setoid_repeats (equiv' data_model (fuel - 1)) (List.Tot.map fst v))
  | _ -> true

and equiv'
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (fuel: nat)
: Tot ((raw_data_item -> raw_data_item -> bool))
  (decreases fuel)
= fun x1 x2 ->
  if data_model x1 x2
  then true
  else if x1 = x2
  then true
  else if 2 + raw_data_item_size x1 + raw_data_item_size x2 > fuel
  then false
  else
    valid' data_model (fuel - 1) x1 && valid' data_model (fuel - 1) x2 &&
    begin match x1, x2 with
    | Array _ v1, Array _ v2 ->
      list_for_all2 (equiv' data_model (fuel - 1)) v1 v2
    | Map _ v1, Map _ v2 ->
      List.Tot.for_all (setoid_assoc_eq (equiv' data_model (fuel - 1)) (equiv' data_model (fuel - 1)) v2) v1 &&
      List.Tot.for_all (setoid_assoc_eq (equiv' data_model (fuel - 1)) (equiv' data_model (fuel - 1)) v1) v2
    | Tagged tag1 v1, Tagged tag2 v2 ->
      tag1.value = tag2.value &&
      equiv' data_model (fuel - 1) v1 v2
    | Int64 ty1 v1, Int64 ty2 v2 ->
      ty1 = ty2 && v1.value = v2.value
    | String ty1 _ v1, String ty2 _ v2 ->
      ty1 = ty2 && v1 = v2
    | _ -> false
    end

let rec valid_incr
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (fuel fuel': nat)
  (x: raw_data_item)
: Lemma
  (requires raw_data_item_size x <= fuel /\ fuel <= fuel')
  (ensures valid' data_model fuel x == valid' data_model fuel' x)
  (decreases fuel)
= match x with
  | Array _ v ->
    list_for_all_ext
      (valid' data_model (fuel - 1))
      (valid' data_model (fuel' - 1))
      v
      (fun y ->
        list_sum_memP raw_data_item_size v y;
        valid_incr data_model (fuel - 1) (fuel' - 1) y
      )
  | Tagged tag v ->
    valid_incr data_model (fuel - 1) (fuel' - 1) v
  | Map _ v ->
    list_for_all_ext
      (valid' data_model (fuel - 1))
      (valid' data_model (fuel' - 1))
      (List.Tot.map fst v)
      (fun y ->
        let y' = list_memP_map_elim fst y v in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y';
        valid_incr data_model (fuel - 1) (fuel' - 1) y
      );
    list_for_all_ext
      (valid' data_model (fuel - 1))
      (valid' data_model (fuel' - 1))
      (List.Tot.map snd v)
      (fun y ->
        let y' = list_memP_map_elim snd y v in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y';
        valid_incr data_model (fuel - 1) (fuel' - 1) y
      );
    list_no_setoid_repeats_ext
      (equiv' data_model (fuel - 1))
      (equiv' data_model (fuel' - 1))
      (List.Tot.map fst v)
      (fun l1 l2 z y ->
        List.Tot.append_length l1 l2;
        let (v1, v2) = List.Tot.splitAt (List.Tot.length l1) v in
        List.Tot.map_append fst v1 v2;
        list_splitAt_append (List.Tot.length l1) v;
        List.Tot.append_length_inv_head l1 l2 (List.Tot.map fst v1) (List.Tot.map fst v2);
        list_sum_append (pair_sum raw_data_item_size raw_data_item_size) v1 v2;
        let z' = list_memP_map_elim fst z v1 in
        let y' = list_memP_map_elim fst y v2 in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v1 z';
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v2 y';
        equiv_incr data_model (fuel - 1) (fuel' - 1) z y
      )
  | _ -> ()

and equiv_incr
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (fuel fuel': nat)
  (x1 x2: raw_data_item)
: Lemma
  (requires 2 + raw_data_item_size x1 + raw_data_item_size x2 <= fuel /\
    fuel <= fuel')
  (ensures equiv' data_model fuel x1 x2 == equiv' data_model fuel' x1 x2)
  (decreases fuel)
= if data_model x1 x2 || x1 = x2
  then ()
  else begin
    valid_incr data_model (fuel - 1) (fuel' - 1) x1;
    valid_incr data_model (fuel - 1) (fuel' - 1) x2;
    match x1, x2 with
    | Array _ v1, Array _ v2 ->
      list_for_all2_ext
        (equiv' data_model (fuel - 1))
        (equiv' data_model (fuel' - 1))
        v1 v2
        (fun y1 y2 ->
          list_sum_memP raw_data_item_size v1 y1;
          list_sum_memP raw_data_item_size v2 y2;
          equiv_incr data_model (fuel - 1) (fuel' - 1) y1 y2;
          ()
        )
    | Tagged tag1 v1, Tagged tag2 v2 ->
      equiv_incr data_model (fuel - 1) (fuel' - 1) v1 v2
    | Map _ v1, Map _ v2 ->
      let prf
        (v1' v2' : list (raw_data_item & raw_data_item))
      : Lemma
        (requires (
          list_sum (pair_sum raw_data_item_size raw_data_item_size) v1' +
          list_sum (pair_sum raw_data_item_size raw_data_item_size) v2' <
            raw_data_item_size x1 + raw_data_item_size x2
        ))
        (ensures (
          List.Tot.for_all (setoid_assoc_eq (equiv' data_model (fuel - 1)) (equiv' data_model (fuel - 1)) v1') v2' ==
          List.Tot.for_all (setoid_assoc_eq (equiv' data_model (fuel' - 1)) (equiv' data_model (fuel' - 1)) v1') v2'
        ))
      =
        list_for_all_ext
          (setoid_assoc_eq (equiv' data_model (fuel - 1)) (equiv' data_model (fuel - 1)) v1')
          (setoid_assoc_eq (equiv' data_model (fuel' - 1)) (equiv' data_model (fuel' - 1)) v1')
          v2'
          (fun z ->
            setoid_assoc_eq_ext
              (equiv' data_model (fuel - 1)) (equiv' data_model (fuel' - 1)) 
              (equiv' data_model (fuel - 1)) (equiv' data_model (fuel' - 1))
              v1'
              z
              (fun y ->
                list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v1' y;
                list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v2' z;
                equiv_incr data_model (fuel - 1) (fuel' - 1) (fst z) (fst y);
                equiv_incr data_model (fuel - 1) (fuel' - 1) (snd z) (snd y);
                ()
              )
          )
      in
      prf v1 v2;
      prf v2 v1
    | _ -> ()
  end

let valid
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= valid' data_model (raw_data_item_size x) x

let equiv
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x1 x2: raw_data_item)
: Tot bool
= equiv' data_model (2 + raw_data_item_size x1 + raw_data_item_size x2) x1 x2

let valid_eq
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
      (list_no_setoid_repeats (equiv data_model) (List.Tot.map fst v))
    | _ -> true
  )))
= match x with
  | Array _ v ->
    list_for_all_ext
      (valid' data_model (raw_data_item_size x - 1))
      (valid data_model)
      v
      (fun y ->
        list_sum_memP raw_data_item_size v y;
        valid_incr data_model (raw_data_item_size y) (raw_data_item_size x - 1) y;
        ()
      )
  | Tagged tag v ->
    valid_incr data_model (raw_data_item_size v) (raw_data_item_size x - 1) v
  | Map _ v ->
    list_for_all_ext
      (valid' data_model (raw_data_item_size x - 1))
      (valid data_model)
      (List.Tot.map fst v)
      (fun y ->
        let y' = list_memP_map_elim fst y v in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y';
        valid_incr data_model (raw_data_item_size y) (raw_data_item_size x - 1) y
      );
    list_for_all_ext
      (valid' data_model (raw_data_item_size x - 1))
      (valid data_model)
      (List.Tot.map snd v)
      (fun y ->
        let y' = list_memP_map_elim snd y v in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y';
        valid_incr data_model (raw_data_item_size y) (raw_data_item_size x - 1) y
      );
    list_no_setoid_repeats_ext
      (equiv' data_model (raw_data_item_size x - 1))
      (equiv data_model)
      (List.Tot.map fst v)
      (fun l1 l2 z y ->
        List.Tot.append_length l1 l2;
        let (v1, v2) = List.Tot.splitAt (List.Tot.length l1) v in
        List.Tot.map_append fst v1 v2;
        list_splitAt_append (List.Tot.length l1) v;
        List.Tot.append_length_inv_head l1 l2 (List.Tot.map fst v1) (List.Tot.map fst v2);
        list_sum_append (pair_sum raw_data_item_size raw_data_item_size) v1 v2;
        let z' = list_memP_map_elim fst z v1 in
        let y' = list_memP_map_elim fst y v2 in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v1 z';
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v2 y';
        equiv_incr data_model (2 + raw_data_item_size z + raw_data_item_size y) (raw_data_item_size x - 1) z y
      )
  | _ -> ()

let equiv_eq
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
= if data_model x1 x2 || x1 = x2
  then ()
  else begin
    valid_incr data_model (raw_data_item_size x1) (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1) x1;
    valid_incr data_model (raw_data_item_size x2) (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1) x2;
    match x1, x2 with
    | Array _ v1, Array _ v2 ->
      list_for_all2_ext
        (equiv' data_model (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1))
        (equiv data_model)
        v1 v2
        (fun y1 y2 ->
          list_sum_memP raw_data_item_size v1 y1;
          list_sum_memP raw_data_item_size v2 y2;
          equiv_incr data_model (2 + raw_data_item_size y1 + raw_data_item_size y2) (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1) y1 y2;
          ()
        )
    | Tagged tag1 v1, Tagged tag2 v2 ->
      equiv_incr data_model (2 + raw_data_item_size v1 + raw_data_item_size v2) (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1) v1 v2
    | Map _ v1, Map _ v2 ->
      let prf
        (v1' v2' : list (raw_data_item & raw_data_item))
      : Lemma
        (requires (
          list_sum (pair_sum raw_data_item_size raw_data_item_size) v1' +
          list_sum (pair_sum raw_data_item_size raw_data_item_size) v2' <
            raw_data_item_size x1 + raw_data_item_size x2
        ))
        (ensures (
          List.Tot.for_all (setoid_assoc_eq (equiv' data_model (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1)) (equiv' data_model (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1)) v1') v2' ==
          List.Tot.for_all (setoid_assoc_eq (equiv data_model) (equiv data_model) v1') v2'
        ))
      =
        list_for_all_ext
          (setoid_assoc_eq (equiv' data_model (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1)) (equiv' data_model (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1)) v1')
          (setoid_assoc_eq (equiv data_model) (equiv data_model) v1')
          v2'
          (fun z ->
            setoid_assoc_eq_ext
              (equiv' data_model (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1)) (equiv data_model) 
              (equiv' data_model (2 + raw_data_item_size x1 + raw_data_item_size x2 - 1)) (equiv data_model)
              v1'
              z
              (fun y ->
                list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v1' y;
                list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v2' z;
                equiv_incr data_model (2 + raw_data_item_size (fst z) + raw_data_item_size (fst y)) (2 + raw_data_item_size x1 + raw_data_item_size x2  - 1) (fst z) (fst y);
                equiv_incr data_model (2 + raw_data_item_size (snd z) + raw_data_item_size (snd y)) (2 + raw_data_item_size x1 + raw_data_item_size x2  - 1) (snd z) (snd y);
                ()
              )
          )
      in
      prf v1 v2;
      prf v2 v1
    | _ -> ()
  end

let equiv_refl
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x1: raw_data_item)
: Lemma
  (ensures equiv data_model x1 x1)
= ()

let rec equiv_sym
  (data_model: (raw_data_item -> raw_data_item -> bool) {
    forall x1 x2 . data_model x1 x2 == data_model x2 x1
  })
  (x1 x2: raw_data_item)
: Lemma
  (ensures equiv data_model x1 x2 == equiv data_model x2 x1)
  (decreases x1)
= equiv_eq data_model x1 x2;
  equiv_eq data_model x2 x1;
  if data_model x1 x2
  then ()
  else if x1 = x2
  then ()
  else if valid data_model x1 && valid data_model x2
  then match x1, x2 with
  | Array _ v1, Array _ v2 ->
    list_for_all2_sym
      (equiv data_model)
      v1 v2
      (fun y1 y2 -> equiv_sym data_model y1 y2)
  | Tagged _ v1, Tagged _ v2 -> equiv_sym data_model v1 v2
  | _ -> ()
  else ()

let abc_cba (a b c: nat) : Lemma
  (a + b + c == c + b + a)
= ()

#push-options "--z3rlimit 16"

let rec equiv_trans'
  (data_model: (raw_data_item -> raw_data_item -> bool) {
    (forall x1 x2 . data_model x1 x2 == data_model x2 x1) /\
    (forall x1 x2 x3 . (data_model x1 x2 /\ equiv data_model x2 x3) ==> data_model x1 x3) /\
    (forall x1 x2 x3 . (equiv data_model x1 x2 /\ data_model x2 x3) ==> data_model x1 x3)
  })
  (x1 x2 x3: raw_data_item)
: Lemma
  (requires (equiv data_model x1 x2 /\ equiv data_model x2 x3))
  (ensures (equiv data_model x1 x3))
  (decreases (raw_data_item_size x1 + raw_data_item_size x2 + raw_data_item_size x3))
= equiv_eq data_model x1 x2;
  equiv_eq data_model x2 x3;
  equiv_eq data_model x1 x3;
  raw_data_item_size_eq x1;
  raw_data_item_size_eq x2;
  raw_data_item_size_eq x3;
  if data_model x1 x2
  then ()
  else if data_model x2 x3
  then ()
  else if x1 = x2
  then ()
  else if x2 = x3
  then ()
  else match x1, x2, x3 with
  | Array _ v1, Array _ v2, Array _ v3 ->
    list_for_all2_trans
      (equiv data_model)
      v1 v2 v3
      (fun y1 y2 y3 ->
        list_sum_memP raw_data_item_size v1 y1;
        list_sum_memP raw_data_item_size v2 y2;
        list_sum_memP raw_data_item_size v3 y3;
        equiv_trans' data_model y1 y2 y3
      )
  | Map _ v1, Map _ v2, Map _ v3 ->
    let prf
      (l1 l2 l3: list (raw_data_item & raw_data_item))
    : Lemma
      (requires (
        list_sum (pair_sum raw_data_item_size raw_data_item_size) l1 +
        list_sum (pair_sum raw_data_item_size raw_data_item_size) l2 +
        list_sum (pair_sum raw_data_item_size raw_data_item_size) l3 ==
        list_sum (pair_sum raw_data_item_size raw_data_item_size) v1 +
        list_sum (pair_sum raw_data_item_size raw_data_item_size) v2 +
        list_sum (pair_sum raw_data_item_size raw_data_item_size) v3 /\
        List.Tot.for_all (setoid_assoc_eq (equiv data_model) (equiv data_model) l1) l2 /\
        List.Tot.for_all (setoid_assoc_eq (equiv data_model) (equiv data_model) l2) l3
      ))
      (ensures (
        List.Tot.for_all (setoid_assoc_eq (equiv data_model) (equiv data_model) l1) l3
      ))
    = list_for_all_intro
        (setoid_assoc_eq (equiv data_model) (equiv data_model) l1)
        l3
        (fun y3 ->
          list_sum_memP
            (pair_sum raw_data_item_size raw_data_item_size)
            l3 y3;
          List.Tot.for_all_mem
            (setoid_assoc_eq (equiv data_model) (equiv data_model) l2)
            l3;
          assert (setoid_assoc_eq (equiv data_model) (equiv data_model) l2 y3);
          let ky3 = fst y3 in
          let Some vy2 = list_setoid_assoc (equiv data_model) ky3 l2 in
          let Some ky2 = list_setoid_assoc_mem (equiv data_model) ky3 l2 in
          let y2 = (ky2, vy2) in
          list_sum_memP
            (pair_sum raw_data_item_size raw_data_item_size)
            l2 y2;
          List.Tot.for_all_mem
            (setoid_assoc_eq (equiv data_model) (equiv data_model) l1)
            l2;
          assert (setoid_assoc_eq (equiv data_model) (equiv data_model) l1 y2);
          let Some vy1 = list_setoid_assoc (equiv data_model) (ky2) l1 in
          let Some ky1 = list_setoid_assoc_mem (equiv data_model) (ky2) l1 in
          let y1 = (ky1, vy1) in
          list_sum_memP
            (pair_sum raw_data_item_size raw_data_item_size)
            l1 y1;
          equiv_trans' data_model (snd y3) vy2 vy1;
          list_setoid_assoc_equiv_gen
            (equiv data_model) (equiv data_model)
            l1
            ky3
            ky2
            (fun a ->
              list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) l1 a;
              let ka = fst a in
              if equiv data_model ky3 ka
              then begin
                equiv_sym data_model ky3 ka;
                equiv_trans' data_model ka ky3 ky2;
                equiv_sym data_model ky2 ka
              end
              else if equiv data_model ky2 ka
              then begin
                equiv_trans' data_model ky3 ky2 ka
              end
              else ()
            );
          ()
        )
    in
    prf v1 v2 v3;
    abc_cba // FIXME: WHY WHY WHY?
      (list_sum (pair_sum raw_data_item_size raw_data_item_size) v1)
      (list_sum (pair_sum raw_data_item_size raw_data_item_size) v2)
      (list_sum (pair_sum raw_data_item_size raw_data_item_size) v3);
    prf v3 v2 v1;
    ()
  | Tagged tag1 v1, Tagged tag2 v2, Tagged tag3 v3 ->
    equiv_trans' data_model v1 v2 v3
  | _ -> ()

#pop-options

let equiv_trans
  (data_model: (raw_data_item -> raw_data_item -> bool) {
    (forall x1 x2 . data_model x1 x2 == data_model x2 x1) /\
    (forall x1 x2 x3 . (data_model x1 x2 /\ equiv data_model x2 x3) ==> data_model x1 x3)
  })
  (x1 x2 x3: raw_data_item)
: Lemma
  (requires (equiv data_model x1 x2 /\ equiv data_model x2 x3))
  (ensures (equiv data_model x1 x3))
= Classical.forall_intro_2 (equiv_sym data_model);
  equiv_trans' data_model x1 x2 x3

let rec valid_eq'
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (ensures (valid data_model x == holds_on_raw_data_item (valid_item data_model) x))
= valid_eq data_model x;
  holds_on_raw_data_item_eq (valid_item data_model) x;
  match x with
  | Array _ v ->
    list_for_all_ext (valid data_model) (holds_on_raw_data_item (valid_item data_model)) v (fun y -> valid_eq' data_model y)
  | Tagged _ v -> valid_eq' data_model v
  | Map _ v ->
    list_of_pair_list_map (valid data_model) v;
    list_for_all_ext
      (holds_on_pair (valid data_model))
      (holds_on_pair (holds_on_raw_data_item (valid_item data_model)))
      v
      (fun x ->
        valid_eq' data_model (fst x);
        valid_eq' data_model (snd x)
      )
  | _ -> ()
