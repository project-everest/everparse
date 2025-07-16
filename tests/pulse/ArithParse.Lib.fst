module ArithParse.Lib
include LowParse.WellFounded

let rec list_sum (#t: Type) (f: t -> nat) (l: list t) : Tot nat =
  match l with
  | [] -> 0
  | a :: q -> f a + list_sum f q

let rec list_sum_memP (#t: Type) (f: t -> nat) (l: list t) (x: t) : Lemma
  (requires (List.Tot.memP x l))
  (ensures (f x <= list_sum f l))
= let a :: q = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (x == a)
  then ()
  else list_sum_memP f q x

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

let rec forall_list_intro (#t: Type) (p: t -> bool) (l: list t)
  (prf: (x: t { List.Tot.memP x l /\ x << l }) -> Lemma (p x))
: Lemma (ensures (forall_list l p))
  (decreases l)
= forall_list_correct p l;
  match l with
  | [] -> ()
  | a :: q -> prf a; forall_list_correct p q; forall_list_intro p q prf
