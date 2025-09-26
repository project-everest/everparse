module CBOR.Spec.Raw.Nondet
include CBOR.Spec.Raw.Valid
open CBOR.Spec.Util

let rec check_equiv_list // this function is tail-recursive, and is meant to be implemented with a loop in a "counter decrease and increase" fashion
  (l1 l2: list raw_data_item)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 }) -> option bool)
: Tot (option bool)
  (decreases (list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2))
= if List.Tot.length l1 <> List.Tot.length l2
  then Some false
  else match l1, l2 with
  | [], [] -> Some true
  | a1 :: q1, a2 :: q2 ->
    raw_data_item_size_eq a1;
    raw_data_item_size_eq a2;
    assert (raw_data_item_size a1 > 0);
    assert (raw_data_item_size a2 > 0);
    let check_tail = check_equiv_list q1 q2 equiv in
    match equiv a1 a2 with
    | None -> None
    | Some b ->
      if b
      then check_tail
      else match a1, a2 with
      | Int64 ty1 v1, Int64 ty2 v2 ->
        if ty1 = ty2 &&
        v1.value = v2.value
        then check_tail
        else Some false
      | Simple v1, Simple v2 ->
        if v1 = v2
        then check_tail
        else Some false
      | String ty1 _ s1, String ty2 _ s2 ->
        if ty1 = ty2 &&
          s1 = s2
        then check_tail
        else Some false
      | Tagged tag1 b1, Tagged tag2 b2 ->
        if tag1.value = tag2.value
        then check_equiv_list (b1 :: q1) (b2 :: q2) equiv
        else Some false
      | Array len1 ar1, Array len2 ar2 ->
        list_sum_append raw_data_item_size ar1 q1;
        list_sum_append raw_data_item_size ar2 q2;
        if len1.value = len2.value
        then check_equiv_list (List.Tot.append ar1 q1) (List.Tot.append ar2 q2) equiv
        else Some false
      | _ -> Some false

let check_equiv_aux
  (bound: nat)
  (equiv: (x1': raw_data_item) -> (x2': raw_data_item { raw_data_item_size x1' + raw_data_item_size x2' <= bound }) -> option bool)
  (x1 x2: raw_data_item)
: Tot (option bool)
= if raw_data_item_size x1 + raw_data_item_size x2 > bound
  then None // dummy
  else check_equiv_list [x1] [x2] equiv

let rec setoid_assoc_eq_with_overflow
  (#t1 #t2: Type)
  (equiv1: t1 -> t1 -> option bool)
  (equiv2: t2 -> t2 -> option bool)
  (ll: list (t1 & t2))
  (xr: (t1 & t2))
: Tot (option bool)
  (decreases ll)
= let (x1, x2) = xr in
  match ll with
  | [] -> Some false
  | (y1, y2) :: q ->
    match equiv1 x1 y1 with
    | None -> None
    | Some true -> equiv2 x2 y2
    | Some false -> setoid_assoc_eq_with_overflow equiv1 equiv2 q xr

let rec list_for_all_with_overflow
  (#t: Type)
  (p: t -> option bool)
  (l: list t)
: Tot (option bool)
= match l with
  | [] -> Some true
  | a :: q ->
    match p a with
    | Some true -> list_for_all_with_overflow p q
    | r -> r

let rec check_equiv_map
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
: Tot (option bool)
  (decreases (match map_bound with None -> raw_data_item_size x1 + raw_data_item_size x2 | Some x -> x)) // this is both a termination proof and a proof that, if the user specifies some map bound, then that bound is a stack bound
= raw_data_item_size_eq x1;
  raw_data_item_size_eq x2;
  if data_model x1 x2
  then Some true
  else match x1, x2 with
  | Map _ v1, Map _ v2 ->
    if map_bound = Some 0
    then None // overflow
    else
      let map_bound' : option nat = (match map_bound with None -> None | Some x -> Some (x - 1)) in
      let bound = list_sum (pair_sum raw_data_item_size raw_data_item_size) v1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) v2 in
      begin match list_for_all_with_overflow (setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map data_model map_bound')) (check_equiv_aux bound (check_equiv_map data_model map_bound')) v2) v1 with
      | Some true ->
        list_for_all_with_overflow (setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map data_model map_bound')) (check_equiv_aux bound (check_equiv_map data_model map_bound')) v1) v2
      | r -> r
      end
  | _ -> Some false

let check_equiv_map'
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
: Tot (option bool)
= raw_data_item_size_eq x1;
  raw_data_item_size_eq x2;
  if data_model x1 x2
  then Some true
  else match x1, x2 with
  | Map _ v1, Map _ v2 ->
    if map_bound = Some 0
    then None // overflow
    else
      let map_bound' : option nat = (match map_bound with None -> None | Some x -> Some (x - 1)) in
      let bound = list_sum (pair_sum raw_data_item_size raw_data_item_size) v1 + list_sum (pair_sum raw_data_item_size raw_data_item_size) v2 in
      begin match list_for_all_with_overflow (setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map data_model map_bound')) (check_equiv_aux bound (check_equiv_map data_model map_bound')) v2) v1 with
      | Some true ->
        list_for_all_with_overflow (setoid_assoc_eq_with_overflow (check_equiv_aux bound (check_equiv_map data_model map_bound')) (check_equiv_aux bound (check_equiv_map data_model map_bound')) v1) v2
      | r -> r
      end
  | _ -> Some false

let check_equiv_map_eq
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
: Tot (squash
    (check_equiv_map data_model map_bound x1 x2 == check_equiv_map' data_model map_bound x1 x2)
  )
= _ by (FStar.Tactics.trefl ())

let check_equiv
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
: Tot (option bool)
= check_equiv_aux (raw_data_item_size x1 + raw_data_item_size x2) (check_equiv_map data_model map_bound) x1 x2

let rec list_existsb_with_overflow
  (#t: Type)
  (p: t -> option bool)
  (l: list t)
: Tot (option bool)
= match l with
  | [] -> Some false
  | a :: q ->
    match p a with
    | Some false -> list_existsb_with_overflow p q
    | r -> r

let rec list_no_setoid_repeats_with_overflow
  (#t: Type)
  (equiv: t -> t -> option bool)
  (l: list t)
: Tot (option bool)
  (decreases l)
= match l with
  | [] -> Some true
  | a :: q ->
    match list_existsb_with_overflow (equiv a) q with
    | Some false ->
      list_no_setoid_repeats_with_overflow equiv q
    | r -> r

let check_valid_item
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x: raw_data_item)
: Tot bool
= match x with
  | Map _ v ->
    Some true = list_no_setoid_repeats_with_overflow
      (check_equiv data_model map_bound)
      (List.Tot.map fst v)
  | _ -> true

let check_valid
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x: raw_data_item)
: Tot bool
= holds_on_raw_data_item (check_valid_item data_model map_bound) x

(** Correctness *)

let rec wf_list_max (#t: Type) (l: list t) (f: (x: t { List.Tot.memP x l /\ x << l }) -> nat) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | a :: q -> 
    let n1 = f a in
    let n2 = wf_list_max q f in
    if n1 > n2 then n1 else n2

let rec wf_list_max_correct (#t: Type) (l: list t) (f: (x: t { List.Tot.memP x l /\ x << l }) -> nat) (x: t) : Lemma
  (ensures (List.Tot.memP x l ==> (x << l /\ f x <= wf_list_max l f)))
  (decreases l)
= Classical.move_requires (List.Tot.memP_precedes x) l;
  match l with
  | [] -> ()
  | _ :: q -> wf_list_max_correct q f x

let rec list_max (#t: Type) (f: t -> nat) (l: list t) : Tot nat =
  match l with
  | [] -> 0
  | a :: q ->
    let n1 = f a in
    let n2 = list_max f q in
    if n1 > n2 then n1 else n2

let rec list_max_append (#t: Type) (f: t -> nat) (l1 l2: list t) : Lemma
  (ensures (
    let n1 = list_max f l1 in
    let n2 = list_max f l2 in
    list_max f (List.Tot.append l1 l2) == (if n1 > n2 then n1 else n2)
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_max_append f q l2

let rec wf_list_max_eq (#t: Type) (f: t -> nat) (l: list t) : Lemma
  (ensures (wf_list_max l f == list_max f l))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> wf_list_max_eq f q

let rec map_depth (x: raw_data_item) : Tot nat =
  match x with
  | Map _ l -> 1 + wf_list_max l map_depth_pair
  | Array _ l -> wf_list_max l map_depth
  | Tagged _ y -> map_depth y
  | _ -> 0

and map_depth_pair (x: (raw_data_item & raw_data_item)) : Tot nat =
  let y1 = map_depth (fst x) in
  let y2 = map_depth (snd x) in
  if y1 > y2 then y1 else y2

let map_depth_eq (x: raw_data_item) : Lemma
  (map_depth x == begin match x with
  | Map _ l -> 1 + list_max map_depth_pair l
  | Array _ l -> list_max map_depth l
  | Tagged _ y -> map_depth y
  | _ -> 0
  end)
= match x with
  | Map len l ->
    assert_norm (map_depth (Map len l) == 1 + wf_list_max l map_depth_pair);
    wf_list_max_eq map_depth_pair l
  | Array len l ->
    assert_norm (map_depth (Array len l) == wf_list_max l map_depth);
    wf_list_max_eq map_depth l
  | _ -> ()

let rec map_key_depth (x: raw_data_item) : Tot nat =
  match x with
  | Map _ l -> wf_list_max l map_key_depth_pair
  | Array _ l -> wf_list_max l map_key_depth
  | Tagged _ y -> map_key_depth y
  | _ -> 0

and map_key_depth_pair (x: (raw_data_item & raw_data_item)) : Tot nat =
  let y1 = map_depth (fst x) in
  let y2 = map_key_depth (snd x) in
  if y1 > y2 then y1 else y2

module Valid = CBOR.Spec.Raw.Valid

let exceeds_bound (a: nat) (b: option nat) : Tot bool =
  match b with
  | None -> false
  | Some b' -> a > b'

let check_equiv_cond
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
  (y: option bool)
: Tot prop
= match y with
  | None -> (map_depth x1 `exceeds_bound` map_bound) \/ (map_depth x2 `exceeds_bound` map_bound)
  | Some v -> v == Valid.equiv data_model x1 x2

let check_equiv_map_cond
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
  (y: option bool)
: Tot prop
= match y with
  | None -> (map_depth x1 `exceeds_bound` map_bound) \/ (map_depth x2 `exceeds_bound` map_bound)
  | Some v -> v == (data_model x1 x2 || (Map? x1 && Map? x2 && Valid.equiv data_model x1 x2))

unfold
let check_equiv_list_precond
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (l1 l2: list raw_data_item)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 }) -> option bool)
: Tot prop
= (List.Tot.for_all (Valid.valid data_model) l1 /\ List.Tot.for_all (Valid.valid data_model) l2) /\
  forall (x1: raw_data_item) (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 }) .
    (Valid.valid data_model x1 /\ Valid.valid data_model x2) ==> (
      check_equiv_map_cond data_model map_bound x1 x2 (equiv x1 x2)
    )

let check_equiv_list_postcond
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (l1 l2: list raw_data_item)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 }) -> option bool)
: Tot prop
= match check_equiv_list l1 l2 equiv with
  | None -> (list_max map_depth l1 `exceeds_bound` map_bound) \/ (list_max map_depth l2 `exceeds_bound` map_bound)
  | Some v -> v == list_for_all2 (Valid.equiv data_model) l1 l2

#push-options "--z3rlimit 32"

let rec check_equiv_list_correct
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (l1 l2: list raw_data_item)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2 }) -> option bool)
: Lemma
  (requires check_equiv_list_precond data_model map_bound l1 l2 equiv)
  (ensures check_equiv_list_postcond data_model map_bound l1 l2 equiv)
  (decreases (list_sum raw_data_item_size l1 + list_sum raw_data_item_size l2))
= Classical.move_requires (list_for_all2_length (Valid.equiv data_model) l1) l2;
  if List.Tot.length l1 <> List.Tot.length l2
  then ()
  else match l1, l2 with
  | [], [] -> ()
  | a1 :: q1, a2 :: q2 ->
    raw_data_item_size_eq a1;
    raw_data_item_size_eq a2;
    check_equiv_list_correct data_model map_bound q1 q2 equiv;
    Valid.equiv_eq data_model a1 a2;
    Valid.valid_eq data_model a1;
    Valid.valid_eq data_model a2;
    map_depth_eq a1;
    map_depth_eq a2;
    match equiv a1 a2 with
    | None -> ()
    | Some true -> ()
    | _ ->
      match a1, a2 with
      | Int64 _ _, Int64 _ _
      | Simple _, Simple _
      | String _ _ _, String _ _ _
        -> ()
      | Tagged tag1 b1, Tagged tag2 b2 ->
        if tag1.value = tag2.value
        then begin
          Valid.equiv_refl data_model b1;
          check_equiv_list_correct data_model map_bound (b1 :: q1) (b2 :: q2) equiv;
          ()
        end
        else ()
      | Array len1 v1, Array len2 v2 ->
        Classical.move_requires (list_for_all2_length (Valid.equiv data_model) v1) v2;
        if len1.value = len2.value
        then begin
          list_for_all2_refl (Valid.equiv data_model) v1 (fun x -> Valid.equiv_refl data_model x);
          list_for_all2_append (Valid.equiv data_model) v1 q1 v2 q2;
          list_sum_append raw_data_item_size v1 q1;
          list_sum_append raw_data_item_size v2 q2;
          List.Tot.for_all_append (Valid.valid data_model) v1 q1;
          List.Tot.for_all_append (Valid.valid data_model) v2 q2;
          list_max_append map_depth v1 q1;
          list_max_append map_depth v2 q2;
          check_equiv_list_correct data_model map_bound (List.Tot.append v1 q1) (List.Tot.append v2 q2) equiv;
          ()
        end
        else ()
      | _ -> ()

#pop-options

unfold
let check_equiv_aux_precond
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
  (x1 x2: raw_data_item)
: Tot prop
= Valid.valid data_model x1 /\ Valid.valid data_model x2 /\
  raw_data_item_size x1 + raw_data_item_size x2 <= bound /\ (
    forall (x1: raw_data_item) (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) .
    (Valid.valid data_model x1 /\ Valid.valid data_model x2) ==>
    check_equiv_map_cond data_model map_bound x1 x2 (equiv x1 x2)
  )

let check_equiv_aux_correct
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (bound: nat)
  (equiv: (x1: raw_data_item) -> (x2: raw_data_item { raw_data_item_size x1 + raw_data_item_size x2 <= bound }) -> option bool)
  (x1 x2: raw_data_item)
: Lemma
  (requires check_equiv_aux_precond data_model map_bound bound equiv x1 x2)
  (ensures check_equiv_cond data_model map_bound x1 x2 (check_equiv_aux bound equiv x1 x2))
= check_equiv_list_correct data_model map_bound [x1] [x2] equiv;
  ()

let check_equiv_map_precond
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
: Tot prop
= Valid.valid data_model x1 /\ Valid.valid data_model x2

let check_equiv_map_correct
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
: Lemma
  (requires check_equiv_map_precond data_model map_bound x1 x2)
  (ensures check_equiv_map_cond data_model map_bound x1 x2 (check_equiv_map data_model map_bound x1 x2))
= admit ()

let check_equiv_precond
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
: Tot prop
= Valid.valid data_model x1 /\ Valid.valid data_model x2

let check_equiv_correct
  (data_model: (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (x1 x2: raw_data_item)
: Lemma
  (requires check_equiv_precond data_model map_bound x1 x2)
  (ensures check_equiv_cond data_model map_bound x1 x2 (check_equiv data_model map_bound x1 x2))
= Classical.forall_intro_2 (fun x1 x2 -> Classical.move_requires (check_equiv_map_correct data_model map_bound x1) x2);
  check_equiv_aux_correct data_model map_bound (raw_data_item_size x1 + raw_data_item_size x2) (check_equiv_map data_model map_bound) x1 x2;
  ()
