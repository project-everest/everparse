module CBOR.Spec.Raw.Set
open CBOR.Spec.Util
open CBOR.Spec.Raw.Map

let t (#elt: eqtype) (f: order elt) : Tot eqtype =
  (l: list elt { List.Tot.sorted f l })

let cardinality (#elt: eqtype) (#f: order elt) (x: t f) : Tot nat =
  List.Tot.length x

let mem (#elt: eqtype) (#f: order elt) (x: elt) (s: t f) : Tot bool =
  List.Tot.mem x s

let ext (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Lemma
  (ensures (equal s1 s2 <==> s1 == s2))
  [SMTPat (equal s1 s2)]
= Classical.move_requires (list_sorted_ext_eq f s1) s2

let empty (#elt: eqtype) (f: order elt) : Tot (t f) =
  []

let mem_empty (#elt: eqtype) (f: order elt) (x: elt) : Lemma
  (ensures (~ (mem x (empty f))))
  [SMTPat (mem x (empty f))]
= ()

let cardinality_empty (#elt: eqtype) (f: order elt) : Lemma
  (ensures (cardinality (empty f) == 0))
  [SMTPat (cardinality (empty f))]
= ()

let singleton (#elt: eqtype) (f: order elt) (x: elt) : Tot (t f) =
  [x]

let mem_singleton (#elt: eqtype) (f: order elt) (x x': elt) : Lemma
  (ensures (mem x' (singleton f x) <==> x' == x))
  [SMTPat (mem x' (singleton f x))]
= ()

let cardinality_singleton (#elt: eqtype) (f: order elt) (x: elt) : Lemma
  (ensures (cardinality (singleton f x) == 1))
  [SMTPat (cardinality (singleton f x))]
= ()

let not_in (#t: eqtype) (l: list t) (x: t) : Tot bool =
  not (List.Tot.mem x l)

let rec total_order_no_repeats_total_order_on_list
  (#t1: Type)
  (key_order: order t1)
  (l: list t1)
: Lemma
  (requires (
    List.Tot.no_repeats_p l
  ))
  (ensures (total_order_on_list key_order l))
= match l with
  | [] -> ()
  | a :: q ->
    total_order_no_repeats_total_order_on_list key_order q

let rec list_sorted_no_repeats
  (#t: Type)
  (f: (t -> t -> bool) {
    order_irrefl f /\
    order_trans f
  })
  (l: list t)
: Lemma
  (requires (List.Tot.sorted f l))
  (ensures (List.Tot.no_repeats_p l))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    Classical.forall_intro (Classical.move_requires (list_sorted_memP f a q));
    list_sorted_no_repeats f q

let union' (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Pure (t f)
  (requires True)
  (ensures (fun s' -> forall x . mem x s' <==> (mem x s1 \/ mem x s2)))
=
  Classical.forall_intro (List.Tot.mem_filter (not_in s1) s2);
  list_sorted_filter f (not_in s1) s2;
  let s2' = List.Tot.filter (not_in s1) s2 in
  list_sorted_no_repeats f s1;
  list_sorted_no_repeats f s2';
  List.Tot.no_repeats_p_append s1 s2';
  List.Tot.append_memP_forall s1 s2';
  let s' = List.Tot.append s1 s2' in
  total_order_no_repeats_total_order_on_list f s';
  list_sortWith_sorted f s';
  list_sortWith f s'

let union (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Tot (t f) =
  union' s1 s2

let mem_union (#elt: eqtype) (#f: order elt) (s1 s2: t f) (x: elt) : Lemma
  (ensures (mem x (union s1 s2) <==> (mem x s1 \/ mem x s2)))
= ()

let rec list_filter_idem
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (forall x . List.Tot.memP x l ==> f x))
  (ensures (List.Tot.filter f l == l))
= match l with
  | [] -> ()
  | _ :: q -> list_filter_idem f q

let cardinality_union (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Lemma
  (requires (disjoint s1 s2))
  (ensures (cardinality (union s1 s2) == cardinality s1 + cardinality s2))
  [SMTPat (cardinality (union s1 s2))]
= 
  Classical.forall_intro (List.Tot.mem_filter (not_in s1) s2);
  list_filter_idem (not_in s1) s2;
  List.Tot.append_length s1 s2;
  list_sortWith_length f (List.Tot.append s1 s2)

let filter (#elt: eqtype) (#f: order elt) (phi: elt -> bool) (s: t f) : Tot (t f) =
  list_sorted_filter f phi s;
  List.Tot.filter phi s

let mem_filter (#elt: eqtype) (#f: order elt) (phi: elt -> bool) (s: t f) (x: elt) : Lemma
  (ensures (mem x (filter phi s) <==> (mem x s /\ phi x)))
  [SMTPat (mem x (filter phi s))]
= List.Tot.mem_filter phi s x

let as_list (#elt: eqtype) (#f: order elt) (s: t f) : GTot (list elt) =
  s

let no_repeats_as_list (#elt: eqtype) (#f: order elt) (s: t f) : Lemma
  (ensures (List.Tot.no_repeats_p (as_list s)))
  [SMTPat (as_list s)]
= list_sorted_no_repeats f s

let mem_as_list (#elt: eqtype) (#f: order elt) (s: t f) (x: elt) : Lemma
  (ensures (List.Tot.memP x (as_list s) <==> mem x s))
  [SMTPat (List.Tot.memP x (as_list s))]
= ()

let length_as_list (#elt: eqtype) (#f: order elt) (s: t f) : Lemma
  (ensures (List.Tot.length (as_list s) == cardinality s))
  [SMTPat (as_list s)]
= ()

let fold (#elt: eqtype) (#u: Type) (#f: order elt) (phi: u -> elt -> u) (x: u) (s: t f) : Tot u =
  List.Tot.fold_left phi x s

let fold_ext
  (#elt: eqtype) (#u: Type) (#f: order elt) (phi1 phi2: u -> elt -> u) (x: u) (s: t f)
: Lemma
  (requires (forall x y . mem y s ==> phi1 x y == phi2 x y))
  (ensures (fold phi1 x s == fold phi2 x s))
= list_fold_ext phi1 phi2 x s

let fold_eq
  (#elt: eqtype) (#u: Type) (#f: order elt) (phi: u -> elt -> u) (x: u) (s: t f) (l: list elt)
: Lemma
  (requires (
    op_comm phi /\
    List.Tot.no_repeats_p l /\
    (forall x . List.Tot.memP x l <==> mem x s)
  ))
  (ensures (
    fold phi x s == List.Tot.fold_left phi x l
  ))
= list_sorted_no_repeats f s;
  list_fold_ext_no_repeats_p phi x s l

let fold_eq_idem
  (#elt: eqtype) (#u: Type) (#f: order elt) (phi: u -> elt -> u) (x: u) (s: t f) (l: list elt)
= list_fold_ext_idem phi x s l
