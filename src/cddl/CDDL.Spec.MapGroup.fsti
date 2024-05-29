module CDDL.Spec.MapGroup
include CDDL.Spec.Base
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Groups in map context (Section 3.5)

[@@erasable]
noeq
type map_group_entry (b: option Cbor.raw_data_item) = | MapGroupEntry: (fst: bounded_typ_gen b) -> (snd: bounded_typ_gen b) -> map_group_entry b

noextract
let opt_map_entry_bounded'
  (b: option Cbor.raw_data_item)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (opt_precedes x b)

module Pull = FStar.Ghost.Pull

let opt_map_entry_bounded
  (b: option Cbor.raw_data_item)
: GTot ((Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
= Pull.pull (opt_map_entry_bounded' b)

let rec opt_precedes_map_for_all_opt_map_entry_bounded
  (b: option Cbor.raw_data_item)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires (opt_precedes l b))
  (ensures (List.Tot.for_all (opt_map_entry_bounded b) l))
  [SMTPat (List.Tot.for_all (opt_map_entry_bounded b) l)]
= match l with
  | [] -> ()
  | _ :: q -> opt_precedes_map_for_all_opt_map_entry_bounded b q

let matches_map_group_entry
  (#b: option Cbor.raw_data_item)
  (ge: map_group_entry b)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item) { opt_map_entry_bounded b x == true })
: GTot bool
= ge.fst (fst x) && ge.snd (snd x)

[@@erasable]
noeq
type map_group (b: option Cbor.raw_data_item) = {
  one: list (map_group_entry b);
  zero_or_one: list (map_group_entry b);
  zero_or_more: list (map_group_entry b);
}

let map_group_empty #b : map_group b = {
  one = [];
  zero_or_one = [];
  zero_or_more = [];
}

let cut_map_group_entry_key
  #b
  (key: bounded_typ_gen b)
  (t: bounded_typ_gen b)
  (x: Cbor.raw_data_item { opt_precedes x b })
: GTot bool
= t x && not (key x)

// Section 3.5.4: Cut
let cut_map_group_entry #b (key: bounded_typ_gen b) (ge: map_group_entry b) : map_group_entry b =
  cut_map_group_entry_key key ge.fst `MapGroupEntry` ge.snd

let cut_map_group #b (key: bounded_typ_gen b) (g: map_group b) : map_group b = {
  one = List.Tot.map (cut_map_group_entry key) g.one;
  zero_or_one = List.Tot.map (cut_map_group_entry key) g.zero_or_one;
  zero_or_more = List.Tot.map (cut_map_group_entry key) g.zero_or_more;
}

let maybe_cut_map_group #b (ge: map_group_entry b) (cut: bool) (g: map_group b) : map_group b =
  if cut
  then cut_map_group (ge.fst) g
  else g

let map_group_cons_one #b (ge: map_group_entry b) (cut: bool) (g: map_group b) : map_group b =
  let g = maybe_cut_map_group ge cut g in {
    g with
    one = ge :: g.one;
  }

let map_group_cons_zero_or_one #b (ge: map_group_entry b) (cut: bool) (g: map_group b) : map_group b =
  let g = maybe_cut_map_group ge cut g in {
    g with
    zero_or_one = ge :: g.zero_or_one;
  }

let map_group_cons_zero_or_more #b (ge: map_group_entry b) (cut: bool) (g: map_group b) : map_group b =
  let g = maybe_cut_map_group ge cut g in {
    g with
    zero_or_more = ge :: g.zero_or_more;
}

val matches_map_group
  (#b: option Cbor.raw_data_item)
  (m: map_group b)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) {List.Tot.for_all (opt_map_entry_bounded b) x })
: GTot bool

val matches_map_group_empty
  (b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (ensures (matches_map_group (map_group_empty #b) x == Nil? x))
  [SMTPat (matches_map_group (map_group_empty #b) x)]

(* Inclusion and equivalence proofs for map groups. Those are meant as the main proof devices for matches_map_group *)

noextract
let is_sub_map_group_of
  #b
  (small large: map_group b)
: Tot prop
= forall x . matches_map_group small x ==> matches_map_group large x

noextract
let map_group_equiv
  #b
  (mg1 mg2: map_group b)
: Tot prop
= forall x . matches_map_group mg1 x == matches_map_group mg2 x

noextract
let is_sub_typ_of
 #b
  (small large: bounded_typ_gen b)
: Tot prop
= forall (x: Cbor.raw_data_item { opt_precedes x b }) . small x ==> large x

noextract
let is_sub_map_group_entry_of
 #b
  (small large: map_group_entry b)
: Tot prop
= small.fst `is_sub_typ_of` large.fst /\
  small.snd `is_sub_typ_of` large.snd

let map_group_ignore_restricted_entries
  #b
  (mg: map_group b)
: Tot (map_group b)
= {mg with
      one = [];
      zero_or_one = [];
  }

let pull_rel
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (x1: t1)
: GTot ((x2: t2) -> Tot bool)
= Pull.pull (fun x2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (r x1 x2))

let list_ghost_forall_exists_body
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (l2: list t2)
: GTot (t1 -> bool)
= Pull.pull (fun x1 -> List.Tot.existsb
    (pull_rel r x1)
    l2
  )

let list_ghost_forall_exists
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (l1: list t1)
  (l2: list t2)
: GTot bool
= List.Tot.for_all
    (list_ghost_forall_exists_body r l2)
    l1

noextract
let matches_map_group_entry'
  (#b: _)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
  (y: map_group_entry b)
: Tot prop
= opt_map_entry_bounded b x ==> matches_map_group_entry y x

val matches_map_group_no_restricted
  (#b: _)
  (g: map_group b)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (
    Nil? g.one /\
    Nil? g.zero_or_one
  ))
  (ensures (
    matches_map_group g x <==> list_ghost_forall_exists matches_map_group_entry' x g.zero_or_more
  ))
  [SMTPat (matches_map_group g x)]

let rec list_ghost_forall2
  (#t1 #t2: Type)
  (f: t1 -> t2 -> GTot prop)
  (l1: list t1)
  (l2: list t2)
: GTot bool
  (decreases l1)
= match l1, l2 with
  | [], [] -> true
  | a1 :: q1, a2 :: q2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (f a1 a2) && list_ghost_forall2 f q1 q2
  | _ -> false

val list_ghost_forall_exists_is_sub_map_group_entry_of_refl
  (#b: _)
  (l: list (map_group_entry b))
: Lemma
  (ensures (list_ghost_forall_exists is_sub_map_group_entry_of l l))
  [SMTPat (list_ghost_forall_exists is_sub_map_group_entry_of l l)]

let map_group_included_zero_or_more
  #b
  (small large: map_group b)
: GTot bool
= list_ghost_forall_exists is_sub_map_group_entry_of small.one large.zero_or_more &&
  list_ghost_forall_exists is_sub_map_group_entry_of small.zero_or_one large.zero_or_more &&
  list_ghost_forall_exists is_sub_map_group_entry_of small.zero_or_more large.zero_or_more &&
  Nil? large.one

val map_group_included_zero_or_more_correct
  (#b: _)
  (small large: map_group b)
: Lemma
  (requires (map_group_included_zero_or_more small large))
  (ensures (is_sub_map_group_of small large))

val map_group_ignore_restricted_entries_sub
  (#b: _)
  (mg: map_group b)
: Lemma
  (requires (
    list_ghost_forall_exists is_sub_map_group_entry_of mg.one mg.zero_or_more /\
    list_ghost_forall_exists is_sub_map_group_entry_of mg.zero_or_one mg.zero_or_more
  ))
  (ensures (
    mg `is_sub_map_group_of` map_group_ignore_restricted_entries mg
  ))

let map_group_ignore_restricted_entries_no_one_equiv
  #b
  (mg: map_group b)
: Lemma
  (requires (
    Nil? mg.one /\
    list_ghost_forall_exists is_sub_map_group_entry_of mg.zero_or_one mg.zero_or_more
  ))
  (ensures (
    map_group_equiv mg (map_group_ignore_restricted_entries mg)
  ))
= map_group_ignore_restricted_entries_sub mg;
  map_group_included_zero_or_more_correct (map_group_ignore_restricted_entries mg) mg

let map_group_included_pointwise
  #b
  (small large: map_group b)
: GTot bool
= list_ghost_forall2 is_sub_map_group_entry_of small.one large.one &&
  list_ghost_forall2 is_sub_map_group_entry_of small.zero_or_one large.zero_or_one &&
  list_ghost_forall2 is_sub_map_group_entry_of small.zero_or_more large.zero_or_more

val map_group_included_pointwise_correct
  (#b: _)
  (small large: map_group b)
: Lemma
  (requires (map_group_included_pointwise small large))
  (ensures (is_sub_map_group_of small large))

let rec list_ghost_forall2_map_l
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (f: t2 -> t1)
  (l: list t2)
: Lemma
  (requires (forall x . r (f x) x))
  (ensures (list_ghost_forall2 r (List.Tot.map f l) l))
= match l with 
  | [] -> ()
  | _ :: q -> list_ghost_forall2_map_l r f q

let rec list_ghost_forall2_map_r
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (f: t1 -> t2)
  (l: list t1)
: Lemma
  (requires (forall x . r x (f x)))
  (ensures (list_ghost_forall2 r l (List.Tot.map f l)))
= match l with 
  | [] -> ()
  | _ :: q -> list_ghost_forall2_map_r r f q

let cut_map_group_sub
  #b
  (key: bounded_typ_gen b)
  (mg: map_group b)
: Lemma
  (cut_map_group key mg `is_sub_map_group_of` mg)
= list_ghost_forall2_map_l is_sub_map_group_entry_of (cut_map_group_entry key) mg.one;
  list_ghost_forall2_map_l is_sub_map_group_entry_of (cut_map_group_entry key) mg.zero_or_one;
  list_ghost_forall2_map_l is_sub_map_group_entry_of (cut_map_group_entry key) mg.zero_or_more;
  map_group_included_pointwise_correct (cut_map_group key mg) mg

(* Proving matches_map_group for sorted maps and map groups where key constraints specify whole elements *)

let rec list_for_all_filter_invariant
  (#t: Type)
  (p: t -> bool)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (List.Tot.for_all p l == true))
  (ensures (List.Tot.for_all p (List.Tot.filter f l) == true))
  [SMTPat (List.Tot.for_all p (List.Tot.filter f l))]
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_filter_invariant p f q

let map_key_neq'
  (#t1 t2: Type)
  (k: t1)
  (x: (t1 & t2))
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (~ (fst x == k))

let map_key_neq
  (#t1 t2: Type)
  (k: t1)
: GTot ((t1 & t2) -> bool)
= Pull.pull (map_key_neq' t2 k)

let map_group_entry_for
  #b
  (k: Cbor.raw_data_item)
  (ty: bounded_typ_gen b)
: Tot (map_group_entry b)
= MapGroupEntry (coerce_to_bounded_typ _ (t_literal k)) ty

let rec list_ghost_assoc_for_all
  (#key: Type)
  (#value: Type)
  (p: (key & value) -> bool)
  (k: key)
  (m: list (key & value))
: Lemma
  (requires (List.Tot.for_all p m == true))
  (ensures (match Cbor.list_ghost_assoc k m with
  | None -> True
  | Some y -> p (k, y)
  ))
  (decreases m)
  [SMTPat (List.Tot.for_all p m); SMTPat (Cbor.list_ghost_assoc k m)]
= match m with
  | [] -> ()
  | (k', _) :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then ()
    else list_ghost_assoc_for_all p k m'

let rec list_assoc_none_for_all_map_key_neq
  (k: Cbor.raw_data_item)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires (None? (Cbor.list_ghost_assoc k l)))
  (ensures (List.Tot.for_all (map_key_neq _ k) l == true))
= match l with
  | [] -> ()
  | _ :: q -> list_assoc_none_for_all_map_key_neq k q

val matches_map_group_map_group_cons_zero_or_one_no_repeats
   (#b: _) (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst x)))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b
    end /\
    matches_map_group (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> matches_map_group g x
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))

val matches_map_group_map_group_cons_one_no_repeats
   (#b: _) (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst x)))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b
    end /\
    matches_map_group (map_group_cons_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> false
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))

val matches_map_group_map_group_cons_zero_or_one_deterministically_encoded_cbor_map_key_order
   (#b: _) (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) x))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b /\ List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) (List.Tot.filter (map_key_neq _ k) x)
    end /\
    matches_map_group (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> matches_map_group g x
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))
  [SMTPat (matches_map_group (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x)]

val matches_map_group_map_group_cons_one_deterministically_encoded_cbor_map_key_order
   (#b: _) (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) x))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b /\ List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) (List.Tot.filter (map_key_neq _ k) x)
    end /\
    matches_map_group (map_group_cons_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> false
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))
  [SMTPat (matches_map_group (map_group_cons_one (map_group_entry_for k ty) true g) x)]

let t_map (#b: option Cbor.raw_data_item) (m: map_group b) : bounded_typ_gen b = fun x ->
  Cbor.Map? x &&
  matches_map_group m (Cbor.Map?.v x)

let t_map_equiv #b (m1 m2: map_group b) : Lemma
  (requires (map_group_equiv m1 m2))
  (ensures (typ_equiv (t_map m1) (t_map m2)))
= ()

let rec t_map_rec
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> map_group (Some b)))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
= Cbor.Map? x &&
  matches_map_group (phi x (t_map_rec phi)) (Cbor.Map?.v x)
