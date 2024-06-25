module CBOR.Spec.Util

let rec list_for_all2 (#t1 #t2: Type) (p: t1 -> t2 -> bool) (l1: list t1) (l2: list t2) : Tot bool (decreases l1) =
  match l1, l2 with
  | [], [] -> true
  | a1 :: q1, a2 :: q2 -> p a1 a2 && list_for_all2 p q1 q2
  | _ -> false

let rec list_for_all2_append (#t1 #t2: Type) (p: t1 -> t2 -> bool) (ll1 lr1: list t1) (ll2 lr2: list t2) : Lemma
  (requires (List.Tot.length ll1 == List.Tot.length ll2))
  (ensures (
    list_for_all2 p (ll1 `List.Tot.append` lr1) (ll2 `List.Tot.append` lr2) ==
      (list_for_all2 p ll1 ll2 && list_for_all2 p lr1 lr2)
  ))
  (decreases ll1)
= match ll1, ll2 with
  | a1 :: q1, a2 :: q2 -> list_for_all2_append p q1 lr1 q2 lr2
  | _ -> ()

noextract
let holds_on_pair2
  (#t: Type)
  (pred: (t -> t -> bool))
  (x: (t & t))
  (y: (t & t))
: Tot bool
= let (x1, x2) = x in
  let (y1, y2) = y in
  pred x1 y1 && pred x2 y2

let list_existsb2
  (#t1 #t2: Type)
  (p: t1 -> t2 -> bool)
  (l2: list t2)
  (x: t1)
: Tot bool
= List.Tot.existsb (p x) l2

let list_for_all_exists (#t1 #t2: Type) (p: t1 -> t2 -> bool) (l1: list t1) (l2: list t2) : bool =
  List.Tot.for_all (list_existsb2 p l2) l1

let rec list_for_all_exists_eq (#t1 #t2: Type) (p: t1 -> t2 -> bool) (l1: list t1) (l2: list t2) : Lemma
  (ensures (list_for_all_exists p l1 l2 == begin match l1 with
  | [] -> true
  | a :: q -> List.Tot.existsb (p a) l2 && list_for_all_exists p q l2
  end))
= match l1 with
  | [] -> ()
  | _ :: q -> list_for_all_exists_eq p q l2

let rec list_existsb_implies
  (#t: Type)
  (p p' : t -> bool)
  (l: list t)
  (prf: (x: t { x << l }) -> Lemma
    (requires (p x == true))
    (ensures (p' x == true))
  )
: Lemma
  (requires (List.Tot.existsb p l == true))
  (ensures (List.Tot.existsb p' l == true))
= match l with
  | a :: q ->
    if p a
    then prf a
    else list_existsb_implies p p' q prf

let list_existsb2_implies
  (#t1 #t2: Type)
  (p p' : t1 -> t2 -> bool)
  (x1: t1)
  (l2: list t2)
  (prf: (x2: t2 { x2 << l2 }) -> Lemma
    (requires (p x1 x2 == true))
    (ensures (p' x1 x2 == true))
  )
: Lemma
  (requires (list_existsb2 p l2 x1 == true))
  (ensures (list_existsb2 p' l2 x1 == true))
= list_existsb_implies (p x1) (p' x1) l2 prf

let rec list_for_all_implies
  (#t: Type)
  (p1 p2: t -> bool)
  (l: list t)
  (prf: (x: t { x << l }) -> Lemma
    (requires (p1 x == true))
    (ensures (p2 x == true))
  )
: Lemma
  (requires (List.Tot.for_all p1 l == true))
  (ensures (List.Tot.for_all p2 l == true))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> prf a; list_for_all_implies p1 p2 q prf

let list_for_all_exists_implies
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
  (prf: (x1: t1) -> (x2: t2 { x1 << l1 /\ x2 << l2 }) -> Lemma
    (requires (p x1 x2 == true))
    (ensures (p' x1 x2 == true))
  )
: Lemma
  (requires (list_for_all_exists p l1 l2 == true))
  (ensures (list_for_all_exists p' l1 l2 == true))
= list_for_all_implies (list_existsb2 p l2) (list_existsb2 p' l2) l1 (fun x1 ->
    list_existsb2_implies p p' x1 l2 (fun x2 -> prf x1 x2)
  )

let list_for_all_exists_ext
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
  (prf: (x1: t1) -> (x2: t2 { x1 << l1 /\ x2 << l2 }) -> Lemma
    (ensures (p' x1 x2 == p x1 x2))
  )
: Lemma
  (ensures (list_for_all_exists p' l1 l2 == list_for_all_exists p l1 l2))
= Classical.move_requires (list_for_all_exists_implies p p' l1 l2) (fun x1 x2 -> prf x1 x2);
  Classical.move_requires (list_for_all_exists_implies p' p l1 l2) (fun x1 x2 -> prf x1 x2)

let andp2 (#t #t': Type) (p1 p2: t -> t' -> bool) (x: t) (x': t') : bool =
  p1 x x' && p2 x x'

let rec list_existsb_elim (#t: Type) (p: t -> bool) (l: list t) : Pure t
  (requires (List.Tot.existsb p l == true))
  (ensures (fun x -> p x == true /\ List.Tot.memP x l))
= let a :: q = l in
  if p a
  then a
  else list_existsb_elim p q

let rec list_existsb_intro (#t: Type) (p: t -> bool) (l: list t) (x: t) : Lemma
  (requires (p x == true /\
    List.Tot.memP x l
  ))
  (ensures (List.Tot.existsb p l == true))
  (decreases l)
= match l with
  | a :: q ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (x == a)
    then ()
    else list_existsb_intro p q x

let prodp (#t1 #t2: Type) (p1: t1 -> bool) (p2: t2 -> bool) (x1: t1) (x2: t2) : bool =
  p1 x1 && p2 x2

let rec list_for_all_exists_prodp (#t1 #t2: Type) (p: t1 -> t2 -> bool) (p1: t1 -> bool) (p2: t2 -> bool) (l1: list t1) (l2: list t2) : Lemma
  (requires (
    List.Tot.for_all p1 l1 == true /\
    List.Tot.for_all p2 l2 == true /\
    list_for_all_exists p l1 l2
  ))
  (ensures (list_for_all_exists (andp2 p (prodp p1 p2)) l1 l2 == true))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a1 :: q1 ->
    let a2 = list_existsb_elim (p a1) l2 in
    List.Tot.for_all_mem p2 l2;
    list_existsb_intro (andp2 p (prodp p1 p2) a1) l2 a2;
    list_for_all_exists_prodp p p1 p2 q1 l2

let rec list_for_all_exists_equal_eq' (#t: eqtype) (l1 l2: list t) (x: t) : Lemma
  (requires (
    list_for_all_exists ( = ) l1 l2 == true /\
    List.Tot.memP x l1
  ))
  (ensures (
    List.Tot.memP x l2
  ))
  (decreases l1)
= let a1 :: q1 = l1 in
  if x = a1
  then
    let x2 = list_existsb_elim ( ( = ) x ) l2 in
    ()
  else
    list_for_all_exists_equal_eq' q1 l2 x

let list_for_all_exists_equal_eq (#t: eqtype) (l1 l2: list t) : Lemma
  (requires (
    list_for_all_exists ( = ) l1 l2 == true
  ))
  (ensures (
    forall x . List.Tot.memP x l1 ==> List.Tot.memP x l2
  ))
= Classical.forall_intro (fun x -> Classical.move_requires (list_for_all_exists_equal_eq' l1 l2) x)

let order_irrefl
  (#t: Type)
  (order: t -> t -> bool)
: Tot prop
= forall x . ~ (order x x)

let order_trans
  (#t: Type)
  (order: t -> t -> bool)
: Tot prop
= forall x y z . (order x y /\ order y z) ==> order x z

let rec list_sorted_memP
  (#t: Type)
  (order: (t -> t -> bool) {
    order_trans order
  })
  (a: t)
  (l: list t)
  (x: t)
: Lemma
  (requires (
    List.Tot.sorted order (a :: l) /\
    List.Tot.memP x l
  ))
  (ensures (order a x == true))
  (decreases l)
= let a' :: l' = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (a' == x)
  then ()
  else list_sorted_memP order a' l' x

let list_sorted_cons_not_memP
  (#t: Type)
  (order: (t -> t -> bool) {
    order_irrefl order /\
    order_trans order
  })
  (a: t)
  (l: list t)
: Lemma
  (requires (
    List.Tot.sorted order (a :: l)
  ))
  (ensures (~ (List.Tot.memP a l)))
= if FStar.StrongExcludedMiddle.strong_excluded_middle (List.Tot.memP a l)
  then list_sorted_memP order a l a
  else ()

let rec list_sorted_ext_eq
  (#t: Type)
  (order: t -> t -> bool {
    order_irrefl order /\
    order_trans order
  })
  (l1 l2: list t)
: Lemma
  (requires (
    List.Tot.sorted order l1 == true /\
    List.Tot.sorted order l2 == true /\
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2)
  ))
  (ensures (
    l1 == l2
  ))
  (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | a1 :: q1, a2 :: q2 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a1 == a2)
    then begin
      list_sorted_cons_not_memP order a1 q1;
      list_sorted_cons_not_memP order a2 q2;
      list_sorted_ext_eq order q1 q2
    end
    else begin
      list_sorted_memP order a2 q2 a1;
      list_sorted_memP order a1 q1 a2
    end
  | a1 :: _, [] -> assert (List.Tot.memP a1 l2)
  | [], a2 :: _ -> assert (List.Tot.memP a2 l1)


let swap (#t1 #t2: Type) (p: t1 -> t2 -> bool) (x2: t2) (x1: t1) : bool =
  p x1 x2

let rec list_for_all2_implies'
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
  (prf: (x: t1) -> (y: t2 { x << l1 /\ List.Tot.memP x l1 /\ y << l2 /\ List.Tot.memP y l2 }) -> Lemma
    (p x y == true ==> p' x y == true)
  )
: Lemma
  (ensures (list_for_all2 p l1 l2 == true ==> list_for_all2 p' l1 l2 == true))
  (decreases l1)
= if list_for_all2 p l1 l2
  then match l1, l2 with
  | [], [] -> ()
  | a1 :: q1, a2 :: q2 ->
    prf a1 a2;
    list_for_all2_implies' p p' q1 q2 prf

let list_for_all2_implies
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
  (prf: (x: t1) -> (y: t2 { x << l1 /\ List.Tot.memP x l1 /\ y << l2 /\ List.Tot.memP y l2 }) -> Lemma
    (requires (p x y == true))
    (ensures (p' x y == true))
  )
: Lemma
  (requires (list_for_all2 p l1 l2 == true))
  (ensures (list_for_all2 p' l1 l2 == true))
= list_for_all2_implies' p p' l1 l2 (fun x y -> if p x y then prf x y else ())

let list_for_all2_ext
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
  (prf: (x: t1) -> (y: t2 { x << l1 /\ List.Tot.memP x l1 /\ y << l2 /\ List.Tot.memP y l2 }) -> Lemma
    (ensures (p' x y == p x y))
  )
: Lemma
  (ensures (list_for_all2 p' l1 l2 == list_for_all2 p l1 l2))
= Classical.move_requires (list_for_all2_implies p p' l1 l2) (fun x y -> prf x y);
  Classical.move_requires (list_for_all2_implies p' p l1 l2) (fun x y -> prf x y)

let rec list_for_all2_swap
  (#t1 #t2: Type)
  (p: t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
: Lemma
  (ensures (list_for_all2 (swap p) l2 l1 == list_for_all2 p l1 l2))
  (decreases l1)
= match l1, l2 with
  | a1 :: q1, a2 :: q2 -> list_for_all2_swap p q1 q2
  | _ -> ()

let rec list_for_all2_sym'
  (#t: Type)
  (p: t -> t -> bool)
  (l1 l2: list t)
  (prf: (x1: t) -> (x2: t { List.Tot.memP x1 l1 /\ x1 << l1 /\ List.Tot.memP x2 l2 /\ x2 << l2 }) -> Lemma
    (requires (p x1 x2 == true))
    (ensures (p x2 x1 == true))
  )
: Lemma
  (requires (list_for_all2 p l1 l2 == true))
  (ensures (list_for_all2 p l2 l1 == true))
= match l1, l2 with
  | x1 :: q1, x2 :: q2 -> prf x1 x2; list_for_all2_sym' p q1 q2 prf
  | _ -> ()

let list_for_all2_sym
  (#t: Type)
  (p: t -> t -> bool)
  (l1 l2: list t)
  (prf: (x1: t) -> (x2: t { List.Tot.memP x1 l1 /\ x1 << l1 /\ List.Tot.memP x2 l2 /\ x2 << l2 }) -> Lemma
    (p x1 x2 == p x2 x1)
  )
: Lemma
  (ensures (list_for_all2 p l1 l2 == list_for_all2 p l2 l1))
= Classical.move_requires (list_for_all2_sym' p l1 l2) (fun x1 x2 -> prf x1 x2);
  Classical.move_requires (list_for_all2_sym' p l2 l1) (fun x2 x1 -> prf x1 x2)

noextract
let holds_on_pair
  (#t: Type)
  (pred: (t -> bool))
  (x: (t & t))
: Tot bool
= let (x1, x2) = x in
  pred x1 && pred x2

let andp (#t: Type) (p1 p2: t -> bool) (x: t) : bool =
  p1 x && p2 x

let holds_on_pair_andp
  (#t: Type)
  (p1 p2: (t -> bool))
  (x: (t & t))
: Lemma
  (holds_on_pair (andp p1 p2) x == (holds_on_pair p1 x && holds_on_pair p2 x))
= ()

let list_for_all_ext
  (#t: Type)
  (p1 p2: t -> bool)
  (l: list t)
  (prf: (x: t { x << l }) -> Lemma
    (p1 x == p2 x)
  )
: Lemma
  (ensures (List.Tot.for_all p1 l == List.Tot.for_all p2 l))
= Classical.move_requires (list_for_all_implies p1 p2 l) (fun x -> prf x);
  Classical.move_requires (list_for_all_implies p2 p1 l) (fun x -> prf x)

let rec list_for_all_andp
  (#t: Type)
  (p1 p2: t -> bool)
  (l: list t)
: Lemma
  (ensures (
    List.Tot.for_all (andp p1 p2) l == (List.Tot.for_all p1 l && List.Tot.for_all p2 l)
  ))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_andp p1 p2 q

let rec list_no_setoid_repeats
  (#t: Type)
  (equiv: t -> t -> bool)
  (l: list t)
: Tot bool
  (decreases l)
= match l with
  | [] -> true
  | a :: q ->
    list_no_setoid_repeats equiv q &&
    not (List.Tot.existsb (equiv a) q)

let rec list_no_setoid_repeats_implies
  (#t: Type)
  (equiv1 equiv2: t -> t -> bool)
  (l: list t)
  (prf: (x1: t) -> (x2: t { List.Tot.memP x1 l /\ List.Tot.memP x2 l /\ x1 << l /\ x2 << l }) -> Lemma
    (requires (equiv2 x1 x2))
    (ensures (equiv1 x1 x2))
  )
: Lemma
  (requires (list_no_setoid_repeats equiv1 l == true))
  (ensures (list_no_setoid_repeats equiv2 l == true))
= match l with
  | [] -> ()
  | a :: q ->
    list_no_setoid_repeats_implies equiv1 equiv2 q prf;
    if List.Tot.existsb (equiv2 a) q
    then begin
      let a' = list_existsb_elim (equiv2 a) q in
      List.Tot.memP_precedes a l;
      List.Tot.memP_precedes a' l;
      prf a a';
      list_existsb_intro (equiv1 a) q a'
    end

let rec list_no_setoid_repeats_noRepeats
  (#t: eqtype)
  (l: list t)
: Lemma
  (list_no_setoid_repeats ( = ) l == List.Tot.noRepeats l)
= match l with
  | [] -> ()
  | a :: q ->
    list_no_setoid_repeats_noRepeats q;
    if List.Tot.existsb (( = ) a) q
    then begin
      let a' = list_existsb_elim (( = ) a) q in
      assert (a == a');
      List.Tot.mem_memP a q
    end
    else if List.Tot.mem a q
    then list_existsb_intro (( = ) a) q a
    else ()

let rec list_no_repeats_noRepeats
  (#t: eqtype)
  (l: list t)
: Lemma
  (List.Tot.noRepeats l == true <==> List.Tot.no_repeats_p l)
= match l with
  | [] -> ()
  | a :: q -> List.Tot.mem_memP a q; list_no_repeats_noRepeats q

let list_no_setoid_repeats_no_repeats
  (#t: eqtype)
  (l: list t)
: Lemma
  (list_no_setoid_repeats ( = ) l == true <==> List.Tot.no_repeats_p l)
= list_no_setoid_repeats_noRepeats l;
  list_no_repeats_noRepeats l

let rec list_for_all2_intro
  (#t1 #t2: Type)
  (p: t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
  (prf: (x: t1) -> (y: t2 { x << l1 /\ List.Tot.memP x l1 /\ y << l2 /\ List.Tot.memP y l2 }) -> Lemma
    (p x y)
  )
: Lemma
  (requires (List.Tot.length l1 == List.Tot.length l2))
  (ensures (list_for_all2 p l1 l2))
  (decreases l1)
= match l1, l2 with
  | a1 :: q1, a2 :: q2 ->
    prf a1 a2;
    list_for_all2_intro p q1 q2 prf
  | _ -> ()

let rec list_for_all2_length
  (#t1 #t2: Type)
  (p: t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
: Lemma
  (requires list_for_all2 p l1 l2 == true)
  (ensures List.Tot.length l1 == List.Tot.length l2)
  (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | _ :: q1, _ :: q2 -> list_for_all2_length p q1 q2

let rec list_for_all2_prod
  (#t1 #t2: Type)
  (p1: t1 -> bool)
  (p2: t2 -> bool)
  (l1: list t1)
  (l2: list t2)
: Lemma
  (requires (
    List.Tot.for_all p1 l1 == true /\
    List.Tot.for_all p2 l2 == true /\
    List.Tot.length l1 == List.Tot.length l2
  ))
  (ensures (
    list_for_all2 (prodp p1 p2) l1 l2 == true
  ))
  (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | _ :: q1, _ :: q2 -> list_for_all2_prod p1 p2 q1 q2

let rec list_for_all2_andp
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
: Lemma
  (ensures (list_for_all2 (andp2 p p') l1 l2 == (list_for_all2 p l1 l2 && list_for_all2 p' l1 l2)))
  (decreases l1)
= match l1, l2 with
  | _ :: q1, _ :: q2 -> list_for_all2_andp p p' q1 q2
  | _ -> ()

let list_for_all2_andp_intro
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> bool)
  (l1: list t1)
  (l2: list t2)
: Lemma
  (requires (
    list_for_all2 p l1 l2 == true /\
    list_for_all2 p' l1 l2 == true
  ))
  (ensures (list_for_all2 (andp2 p p') l1 l2 == true))
= list_for_all2_andp p p' l1 l2

let rec list_for_all2_equals (#t: eqtype) (l1 l2: list t) : Lemma
  (requires (list_for_all2 ( = ) l1 l2 == true))
  (ensures (l1 == l2))
  (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | _ :: q1, _ :: q2 -> list_for_all2_equals q1 q2

let prod_or (#t1 #t2: Type) (p1: t1 -> bool) (p2: t2 -> bool) (x1: t1) (x2: t2) : Tot bool =
  p1 x1 || p2 x2

let rec list_for_all2_prod_or_weak
  (#t1 #t2: Type)
  (p1: t1 -> bool) (p2: t2 -> bool)
  (l1: list t1)
  (l2: list t2)
: Lemma
  (requires (
    List.Tot.length l1 == List.Tot.length l2 /\ (
    List.Tot.for_all p1 l1 == true \/
    List.Tot.for_all p2 l2 == true
  )))
  (ensures (
    list_for_all2 (prod_or p1 p2) l1 l2 == true
  ))
= match l1, l2 with
  | _ :: q1, _ :: q2 -> list_for_all2_prod_or_weak p1 p2 q1 q2
  | _ -> ()

let rec list_sum (#t: Type) (f: t -> nat) (l: list t) : Tot nat =
  match l with
  | [] -> 0
  | a :: q -> f a + list_sum f q

let rec list_sum_append (#t: Type) (f: t -> nat) (l1 l2: list t) : Lemma
  (ensures (list_sum f (l1 `List.Tot.append` l2) == list_sum f l1 + list_sum f l2))
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_sum_append f q l2

let rec list_sum_ext (#t: Type) (f1 f2: t -> nat) (l: list t) (prf: (x: t { List.Tot.memP x l /\ x << l }) -> Lemma
  (f1 x == f2 x)
)
  : Lemma
  (ensures (list_sum f1 l == list_sum f2 l))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> prf a; list_sum_ext f1 f2 q prf

let pair_sum (#t1: Type) (#t2: Type) (f1: t1 -> nat) (f2: t2 -> nat) (x: (t1 & t2)) : Tot nat =
  f1 (fst x) + f2 (snd x)

let rec list_of_pair_list
  (#t: Type)
  (x: list (t & t))
: Tot (list t)
= match x with
  | [] -> []
  | (a, b) :: q -> a :: b :: list_of_pair_list q

let rec list_of_pair_list_sum
  (#t: Type)
  (f: t -> nat)
  (l: list (t & t))
: Lemma
  (list_sum (pair_sum f f) l == list_sum f (list_of_pair_list l))
= match l with
  | [] -> ()
  | _ :: q -> list_of_pair_list_sum f q

let rec list_of_pair_list_for_all
  (#t: Type)
  (f: t -> bool)
  (l: list (t & t))
: Lemma
  (List.Tot.for_all (holds_on_pair f) l == List.Tot.for_all f (list_of_pair_list l))
= match l with
  | [] -> ()
  | _ :: q -> list_of_pair_list_for_all f q

let rec list_of_pair_list_length
  (#t: Type)
  (l: list (t & t))
: Lemma
  (List.Tot.length (list_of_pair_list l) == (let len = List.Tot.length l in len + len))
= match l with
  | [] -> ()
  | _ :: q -> list_of_pair_list_length q

let apply_on_pair (#a #b: Type) (f: a -> b) (x: (a & a)) : Tot (b & b) =
  (f (fst x), f (snd x))

let rec list_map_ext (#t #t': Type) (f1 f2: t -> t') (l: list t) (prf: (x: t { List.Tot.memP x l /\ x << l }) -> Lemma
  (f1 x == f2 x)
) : Lemma
  (List.Tot.map f1 l == List.Tot.map f2 l)
= match l with
  | [] -> ()
  | a :: q -> prf a; list_map_ext f1 f2 q prf

(* Well-founded recursion *)

let rec wf_list_for_all (#t: Type) (l: list t) (p: (x: t { x << l }) -> bool) : bool =
  match l with
  | [] -> true
  | a :: q -> p a && wf_list_for_all q p

let rec wf_list_for_all_eq (#t: Type) (p: t -> bool) (l: list t) : Lemma
  (ensures wf_list_for_all l p == List.Tot.for_all p l)
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> wf_list_for_all_eq p q

let rec wf_list_existsb (#t: Type) (l: list t) (p: (x: t { x << l }) -> bool) : bool =
  match l with
  | [] -> false
  | a :: q -> p a || wf_list_existsb q p

let rec wf_list_existsb_eq (#t: Type) (p: t -> bool) (l: list t) : Lemma
  (ensures wf_list_existsb l p == List.Tot.existsb p l)
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    if p a
    then ()
    else wf_list_existsb_eq p q

let rec wf_list_for_all2 (#t1 #t2: Type) (l1: list t1) (l2: list t2) (p: (x1: t1) -> (x2: t2 { x1 << l1 /\ x2 << l2 }) -> bool) : Tot bool
  (decreases l1)
=
  match l1, l2 with
  | [], [] -> true
  | a1 :: q1, a2 :: q2 -> p a1 a2 && wf_list_for_all2 q1 q2 p
  | _ -> false

let rec wf_list_for_all2_eq (#t1 #t2: Type) (p: t1 -> t2 -> bool) (l1: list t1) (l2: list t2) : Lemma
    (ensures (wf_list_for_all2 l1 l2 p == list_for_all2 p l1 l2))
    (decreases l1)
= match l1, l2 with
  | a1 :: q1, a2 :: q2 -> wf_list_for_all2_eq p q1 q2
  | _ -> ()

let rec wf_list_for_all_exists (#t1 #t2: Type) (l1: list t1) (l2: list t2) (p: (x1: t1) -> (x2: t2 { x1 << l1 /\ x2 << l2 }) -> bool) : Tot bool
    (decreases l1)
= match l1 with
  | [] -> true
  | a :: q -> wf_list_existsb l2 (p a) && wf_list_for_all_exists q l2 p

let rec wf_list_for_all_exists_eq (#t1 #t2: Type) (p: t1 -> t2 -> bool) (l1: list t1) (l2: list t2) : Lemma
    (ensures wf_list_for_all_exists l1 l2 p == list_for_all_exists p l1 l2)
    (decreases l1)
= list_for_all_exists_eq p l1 l2;
  match l1 with
  | [] -> ()
  | a :: q ->
    wf_list_existsb_eq (p a) l2;
    wf_list_for_all_exists_eq p q l2

let notp (#t: Type) (p: t -> bool) (x: t) : Tot bool =
  not (p x)

let rec wf_list_sum (#t: Type) (l: list t) (f: (x: t { List.Tot.memP x l /\ x << l }) -> nat) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | a :: q -> f a + wf_list_sum q f

let rec wf_list_sum_eq (#t: Type) (f: t -> nat) (l: list t) : Lemma
  (ensures (wf_list_sum l f == list_sum f l))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> wf_list_sum_eq f q

let rec wf_list_map (#t1 #t2: Type) (l: list t1) (f: (x1: t1 { List.Tot.memP x1 l /\ x1 << l }) -> t2) : Tot (list t2) =
  match l with
  | [] -> []
  | a :: q -> f a :: wf_list_map q f

let rec wf_list_map_eq (#t1 #t2: Type) (f: t1 -> t2) (l: list t1) : Lemma
  (wf_list_map l f == List.Tot.map f l)
= match l with
  | [] -> ()
  | _ :: q -> wf_list_map_eq f q

let rec wf_list_map_length (#t1 #t2: Type) (l: list t1) (f: (x1: t1 { List.Tot.memP x1 l /\ x1 << l }) -> t2) : Lemma
  (ensures (List.Tot.length (wf_list_map l f) == List.Tot.length l))
  [SMTPat (List.Tot.length (wf_list_map l f))]
= match l with
  | [] -> ()
  | _ :: q -> wf_list_map_length q f
