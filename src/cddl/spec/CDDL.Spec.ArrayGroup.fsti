module CDDL.Spec.ArrayGroup
include CDDL.Spec.Base
module Cbor = CBOR.Spec.API.Type
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Section 2.1: Groups 

// Groups in array context (Section 3.4)

// Greedy semantics (Appendix A)

let list_is_suffix_of
  (#t: Type)
  (small large: list t)
: Tot prop
= exists prefix . large == prefix `List.Tot.append` small

let list_is_suffix_of_refl
  (#t: Type)
  (l: list t)
: Lemma
  (l `list_is_suffix_of` l)
  [SMTPat (l `list_is_suffix_of` l)]
= assert (l == [] `List.Tot.append` l)

let rec list_nil_precedes
  (#t: Type)
  (l: list t)
: Lemma
  (Nil #t == l \/ Nil #t << l)
= match l with
  | [] -> ()
  | a :: q -> list_nil_precedes q

let rec list_is_suffix_of_precedes
  (#t0 #t: Type)
  (v0: t0)
  (small large: list t)
: Lemma
  (requires (
    large << v0 /\
    small `list_is_suffix_of` large
  ))
  (ensures (
    small << v0
  ))
  (decreases (List.Tot.length large))
  [SMTPat [small << v0]; SMTPat [small `list_is_suffix_of` large]]
= if Nil? small
  then list_nil_precedes large
  else begin
    let prefix = FStar.IndefiniteDescription.indefinite_description_ghost (list t) (fun prefix -> large == prefix `List.Tot.append` small) in
    List.Tot.append_length prefix small;
    if List.Tot.length small = List.Tot.length large
    then ()
    else list_is_suffix_of_precedes v0 small (List.Tot.tl large)
  end

let opt_precedes_list_item
  (#t1 #t2: Type)
  (x2: option t2)
  (x1: t1)
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (opt_precedes x1 x2)

noextract
let opt_precedes_list
  (#t1 #t2: Type)
  (l: list t1)
  (b: option t2)
: Tot prop
= forall (x: t1) . List.Tot.memP x l ==> opt_precedes x b

let rec opt_precedes_opt_precedes_list
  (#t1 #t2: Type)
  (l: list t1)
  (b: option t2)
: Lemma
  (requires (opt_precedes l b))
  (ensures (opt_precedes_list l b))
  [SMTPat (opt_precedes_list l b)]
= match l with
  | [] -> ()
  | a :: q -> opt_precedes_opt_precedes_list q b

[@@ noextract_to "krml"]
let array_group (bound: option Cbor.cbor) = (l: list Cbor.cbor { opt_precedes_list l bound }) -> Pure (option (list Cbor.cbor & list Cbor.cbor))
  (requires True)
  (ensures (fun l' -> match l' with
  | None -> True
  | Some (l1, l2) -> l == l1 `List.Tot.append` l2
  ))

noextract
let array_group_equiv
  #b
  (g1 g2: array_group b)
: Tot prop
= forall l . g1 l == g2 l

let array_group_always_false #b : array_group b = fun _ -> None

let rec opt_precedes_list_assoc
  (#t1 #t2: Type)
  (l1 l2: list t1)
  (b: option t2)
: Lemma
  (opt_precedes_list (l1 `List.Tot.append` l2) b <==>  opt_precedes_list l1 b /\ opt_precedes_list l2 b)
  [SMTPat (opt_precedes_list (l1 `List.Tot.append` l2) b)]
= match l1 with
  | [] -> ()
  | _ :: q1 -> opt_precedes_list_assoc q1 l2 b

let array_group_empty #b : array_group b = fun x -> Some ([], x)
let array_group_concat #b (a1 a3: array_group b) : array_group b =
  (fun l ->
    match a1 l with
    | None -> None
    | Some (l1, l2) ->  begin match a3 l2 with
      | None -> None
      | Some (l3, l4) -> List.Tot.append_assoc l1 l3 l4; Some (List.Tot.append l1 l3, l4)
    end
  )

let array_group_concat_equiv
  #b
  (a1 a1' a2 a2' : array_group b)
: Lemma
  (requires ((a1 `array_group_equiv` a1') /\ (a2 `array_group_equiv` a2')))
  (ensures ((a1 `array_group_concat` a2) `array_group_equiv` (a1' `array_group_concat` a2')))
= ()

val array_group_concat_assoc
  (#b: _)
  (a1 a2 a3: array_group b)
: Lemma
  (array_group_concat a1 (array_group_concat a2 a3) `array_group_equiv`
    array_group_concat (array_group_concat a1 a2) a3)
  [SMTPatOr [
//    [SMTPat (array_group_concat a1 (array_group_concat a2 a3))];
    [SMTPat (array_group_concat (array_group_concat a1 a2) a3)]
  ]]

let array_group_concat_unique_strong
  #b (a1 a3: array_group b)
: Tot prop
= (forall (l: (l: list Cbor.cbor { opt_precedes_list l b })) (l' rem: list Cbor.cbor) .
    array_group_concat a1 a3 l == Some (l', rem) <==> (
      (exists (l1 l2 l3: list Cbor.cbor) .
        l == l1 `List.Tot.append` l2 /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l3, rem) /\
        l' == l1 `List.Tot.append` l3
  ))) /\
  (forall (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) /\ Some? (a3 l2)) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
  )

let array_group_concat_unique_strong_equiv
  #b (a1 a1' a3 a3': array_group b)
: Lemma
  (requires (
    array_group_equiv a1 a1' /\
    array_group_equiv a3 a3'
  ))
  (ensures (
    array_group_concat_unique_strong a1 a3 <==>
    array_group_concat_unique_strong a1' a3'
  ))
= array_group_concat_equiv a1 a1' a3 a3'

let array_group_strong_prefix
  #b (a1: array_group b)
: Tot prop
= forall (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) <==> a1 (l1 `List.Tot.append` l2) == Some (l1, l2))

val array_group_concat_unique_strong_strong_prefix
  (#b: _) (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a2 /\
    array_group_strong_prefix a2
  ))
  (ensures (
    array_group_strong_prefix (array_group_concat a1 a2)
  ))

let array_group_choice #b (a1 a3: array_group b) : array_group b =
  fun l -> match a1 l with
    | None -> a3 l
    | Some l3 -> Some l3

let array_group_disjoint #b (a1 a2: array_group b) : Tot prop
= (forall (l: list Cbor.cbor { opt_precedes_list l b }) . ~ (Some? (a1 l) /\ Some? (a2 l)))

val array_group_concat_unique_strong_choice_left #b (a1 a2 a3: array_group b) : Lemma
  (requires (
    array_group_concat_unique_strong a1 a3 /\
    array_group_concat_unique_strong a2 a3 /\
    array_group_disjoint a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong (array_group_choice a1 a2) a3
  ))

let rec array_group_zero_or_more' #b (a: array_group b) (l: list Cbor.cbor { opt_precedes_list l b }) : Pure (option (list Cbor.cbor & list Cbor.cbor))
  (requires True)
  (ensures (fun l' -> match l' with None -> True | Some (l1, l2) -> l == l1 `List.Tot.append` l2))
  (decreases (List.Tot.length l))
=
  match a l with
  | None -> Some ([], l)
  | Some (l1, l2) ->
    List.Tot.append_length l1 l2;
    if Nil? l1
    then Some (l1, l2)
    else
      begin match array_group_zero_or_more' a l2 with
      | None -> None
      | Some (l2', l3) -> List.Tot.append_assoc l1 l2' l3; Some (List.Tot.append l1 l2', l3)
      end

let array_group_zero_or_more #b : array_group b -> array_group b = array_group_zero_or_more'

let array_group_zero_or_more_eq #b (a: array_group b) (l: list Cbor.cbor { opt_precedes_list l b }) : Lemma
  (array_group_zero_or_more a l == (
  match a l with
  | None -> Some ([], l)
  | Some (l1, l2) ->
    if Nil? l1
    then Some (l1, l2)
    else
      begin match array_group_zero_or_more a l2 with
      | None -> None
      | Some (l2', l3) -> Some (List.Tot.append l1 l2', l3)
      end
  ))
= ()

val array_group_zero_or_more_some
  (#b: _)
  (a: array_group b)
  (l: list Cbor.cbor { opt_precedes_list l b })
: Lemma
  (ensures (Some? (array_group_zero_or_more a l)))
  [SMTPat (array_group_zero_or_more a l)]

val array_group_zero_or_more_equiv (#b: _)
 (a1 a2: array_group b)
: Lemma
  (requires array_group_equiv a1 a2)
  (ensures array_group_equiv (array_group_zero_or_more a1) (array_group_zero_or_more a2))
  [SMTPat (array_group_equiv (array_group_zero_or_more a1) (array_group_zero_or_more a2))]

val array_group_concat_unique_strong_zero_or_more_left
  (#b: _) (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_concat_unique_strong a1 a1 /\
    array_group_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong (array_group_zero_or_more a1) a2
  ))

let array_group_concat_unique_weak
  #b (a1 a3: array_group b)
: Tot prop
= (forall (l: (l: list Cbor.cbor { opt_precedes_list l b })) .
    array_group_concat a1 a3 l == Some (l, []) ==> (
      (exists (l1 l2: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
  ))) /\
  (forall (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
  )

let array_group_concat_unique_weak_elim1
  #b (a1 a3: array_group b)
  (l: list Cbor.cbor { opt_precedes_list l b })
: Lemma
  (requires (
    array_group_concat_unique_weak a1 a3 /\
    array_group_concat a1 a3 l == Some (l, [])
  ))
  (ensures (
      exists (l1 l2: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
  ))
= ()

let array_group_concat_unique_weak_elim2
  #b (a1 a3: array_group b)
  (l1 l2: (l: list Cbor.cbor { opt_precedes_list l b }))
: Lemma
  (requires (
    array_group_concat_unique_weak a1 a3 /\
    a1 l1 == Some (l1, []) /\
    a3 l2 == Some (l2, [])
  ))
  (ensures a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
= ()

val array_group_concat_unique_weak_intro
  (#b: _) (a1 a3: array_group b)
  (prf1:
    (l: (l: list Cbor.cbor { opt_precedes_list l b })) ->
    Lemma
    (requires array_group_concat a1 a3 l == Some (l, []))
    (ensures
      (exists (l1 l2: list Cbor.cbor) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))
//    [SMTPat (array_group_concat a1 a3 l)]
  )
  (prf2:
    (l1: (l: list Cbor.cbor { opt_precedes_list l b })) ->
    (l2: (l: list Cbor.cbor { opt_precedes_list l b })) ->
    Lemma
    (requires
        a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])
    )
    (ensures       
      a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
    )
//    [SMTPat (a1 (l1 `List.Tot.append` l2))]
  )
: Lemma
  (array_group_concat_unique_weak a1 a3)

let list_append_l_nil
  (#t: Type)
  (l: list t)
: Lemma
  (l `List.Tot.append` [] == l)
  [SMTPat (l `List.Tot.append` [])]
= List.Tot.append_l_nil l

let close_array_group
  (#b: _)
  (t: array_group b)
: Tot (array_group b)
= fun l ->
    let res = t l in
    match res with
    | Some (_, []) -> res
    | _ -> None

val array_group_concat_unique_weak_zero_or_more_left
  (#b: _) (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 (close_array_group a2) /\
    array_group_concat_unique_strong a1 a1 /\
    array_group_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_zero_or_more a1) a2
  ))

val array_group_concat_unique_weak_zero_or_more_right
  (#b: _) (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak a1 (array_group_zero_or_more a2)
  ))

val array_group_concat_unique_weak_zero_or_more
  (#b: _) (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_concat_unique_strong a1 a1 /\
    array_group_concat_unique_strong a1 a2 /\
    array_group_disjoint a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_zero_or_more a1) (array_group_zero_or_more a2)
  ))

val array_group_concat_unique_weak_choice_right #b (a1 a2 a3: array_group b) : Lemma
  (requires (
    array_group_concat_unique_weak a1 a2 /\
    array_group_concat_unique_weak a1 a3
  ))
  (ensures (
    array_group_concat_unique_weak a1 (array_group_choice a2 a3)
  ))

let array_group_concat_unique_weak_choice_left #b (a1 a2 a3: array_group b) : Lemma
  (requires (
    array_group_concat_unique_weak a1 a3 /\
    array_group_concat_unique_weak a2 a3 /\
    array_group_disjoint a1 (close_array_group (array_group_concat a2 a3)) /\
    array_group_disjoint (a1) (close_array_group a2)
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_choice a1 a2) a3
  ))
= ()

#restart-solver
let array_group_concat_unique_weak_concat_left
  (g1 g2 g3: array_group None)
: Lemma
  (requires
    array_group_concat_unique_weak g1 g2 /\
    array_group_concat_unique_weak g2 g3 /\    
    array_group_concat_unique_weak g1 (g2 `array_group_concat` g3)
  )
  (ensures
    array_group_concat_unique_weak (g1 `array_group_concat` g2) g3
  )
=   let a1 = g1 `array_group_concat` g2 in
    let a3 = g3 in
    array_group_concat_unique_weak_intro a1 a3
      (fun l -> ())
      (fun l1 l2 ->
        let Some (l1l, l1r) = g1 l1 in
        List.Tot.append_assoc l1l l1r l2
      );
    assert (array_group_concat_unique_weak a1 a3)

let array_group_concat_unique_weak_close_right
  (g1 g2: array_group None)
: Lemma
  (array_group_concat_unique_weak g1 (close_array_group g2) <==> array_group_concat_unique_weak g1 g2)
= ()

let array_group_one_or_more #b (a: array_group b) : array_group b =
  a `array_group_concat` array_group_zero_or_more a

let array_group_one_or_more_equiv #b
 (a1 a2: array_group b)
: Lemma
  (requires array_group_equiv a1 a2)
  (ensures array_group_equiv (array_group_one_or_more a1) (array_group_one_or_more a2))
  [SMTPat (array_group_equiv (array_group_one_or_more a1) (array_group_one_or_more a2))]
= array_group_zero_or_more_equiv a1 a2

let array_group_zero_or_one #b (a: array_group b) : Tot (array_group b) =
  a `array_group_choice` array_group_empty

val array_group_concat_unique_strong_concat_left
  (#b: _)
  (g1 g2 g3: array_group b)
: Lemma
  (requires
    array_group_concat_unique_strong g1 (array_group_concat g2 g3) /\
    array_group_concat_unique_strong g2 g3 /\
    array_group_concat_unique_weak g1 g2
  )
  (ensures
    array_group_concat_unique_strong (array_group_concat g1 g2) g3
  )

val array_group_concat_unique_strong_zero_or_one_left
  (#b: _) (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong (array_group_zero_or_one a1) a2
  ))

val array_group_concat_unique_strong_one_or_more_left
  (#b: _) (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2 /\
    array_group_concat_unique_strong a1 a1 /\
    array_group_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group_concat_unique_strong (array_group_one_or_more a1) a2
  ))

#restart-solver
let array_group_concat_unique_weak_zero_or_one_left
  #b (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 (close_array_group a2) /\
    array_group_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_zero_or_one a1) a2
  ))
= ()

val array_group_concat_unique_weak_one_or_more_left
  (#b: _) (a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 (close_array_group a2) /\
    array_group_concat_unique_strong a1 a1 /\
    array_group_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group_concat_unique_weak (array_group_one_or_more a1) a2
  ))

let array_group_item (#b: option Cbor.cbor) (t: bounded_typ_gen b) : array_group b = fun l ->
  match l with
  | [] -> None
  | a :: q -> if t a then Some ([a], q) else None

let array_group_item_equiv
  #b
  (t1 t2: bounded_typ_gen b)
: Lemma
  (requires (t1 `typ_equiv` t2))
  (ensures (array_group_item t1 `array_group_equiv` array_group_item t2))
= ()

let match_array_group (#b: option Cbor.cbor) (a: array_group b)
  (l: list Cbor.cbor {opt_precedes_list l b})
: Tot bool
= match a l with
  | Some (_, l') -> Nil? l'
  | _ -> false

let t_array (#b: option Cbor.cbor) (a: array_group b) : bounded_typ_gen b = fun w -> let x = Cbor.unpack w in
  Cbor.CArray? x &&
  match_array_group a (Cbor.CArray?.v x)

let t_array_equiv
  #b
  (a1 a2: array_group b)
: Lemma
  (requires (array_group_equiv a1 a2))
  (ensures (typ_equiv (t_array a1) (t_array a2)))
= ()

let maybe_close_array_group
  (#b: _)
  (t: array_group b)
  (close: bool)
: Tot (array_group b)
= if close
  then close_array_group t
  else t

let array_close_array_group
  (#b: _)
  (a: array_group b)
: Lemma
  (typ_equiv
    (t_array a)
    (t_array (close_array_group a))
  )
= ()

let array_group_equiv_close_concat
  #b
  (a1 a2: array_group b)
: Lemma
  (array_group_equiv (close_array_group (array_group_concat a1 a2)) (array_group_concat a1 (close_array_group a2)))
= ()

let array_group_included #b (a1 a2: array_group b) : Tot prop
= (forall (l: list Cbor.cbor { opt_precedes_list l b }) .
    match a1 l with
    | None -> True
    | Some _ -> a2 l == a1 l
  )

let array_group_included_refl
  (#b: _)
  (a: array_group b)
: Lemma
  (array_group_included a a)
= ()

let array_group_included_trans
  (#b: _)
  (a1 a2 a3: array_group b)
: Lemma
  (requires (array_group_included a1 a2 /\ array_group_included a2 a3))
  (ensures (array_group_included a1 a3))
= ()

let t_array_included
  (a1 a2: array_group None)
: Lemma
  (requires (array_group_included (close_array_group a1) (close_array_group a2)))
  (ensures (typ_included (t_array a1) (t_array a2)))
= ()

let array_group_included_concat_item
  (t1 t2: typ)
  (a1 a2: array_group None)
: Lemma
  (requires (typ_included t1 t2 /\ array_group_included a1 a2))
  (ensures (array_group_included (array_group_concat (array_group_item t1) a1) (array_group_concat (array_group_item t2) a2)))
= ()

let array_group_included_zero_or_more_1_aux
  (#b: _)
  (a1 a2: array_group b)
: Lemma
  (ensures (
    array_group_included (array_group_concat a1 (array_group_concat (array_group_zero_or_more a1) a2)) (array_group_concat (array_group_zero_or_more a1) a2)
  ))
= array_group_concat_assoc a1 (array_group_zero_or_more a1) a2

let array_group_included_zero_or_more_1
  (#b: _)
  (a a1 a2: array_group b)
: Lemma
  (requires (
    array_group_included a (array_group_concat a1 (array_group_concat (array_group_zero_or_more a1) a2))
  ))
  (ensures (
    array_group_included a (array_group_concat (array_group_zero_or_more a1) a2)
  ))
= array_group_included_zero_or_more_1_aux a1 a2

let array_group_included_zero_or_more_2
  (#b: _)
  (a a1 a2: array_group b)
: Lemma
  (requires (
    array_group_disjoint a a1 /\ // necessary because of the greedy semantics
    array_group_included a a2
  ))
  (ensures (
    array_group_included a (array_group_concat (array_group_zero_or_more a1) a2)
  ))
= ()

let rec array_group_included_zero_or_more_l_aux
  (#b: _)
  (al ar al' ar': array_group b)
  (l: list Cbor.cbor { opt_precedes_list l b })
: Lemma
  (requires (
    array_group_included al al' /\
    array_group_included ar (array_group_concat (array_group_zero_or_more al') ar') /\
    Some? (array_group_concat (array_group_zero_or_more al) ar l)
  ))
  (ensures
    array_group_concat (array_group_zero_or_more al) ar l == array_group_concat (array_group_zero_or_more al') ar' l
  )
  (decreases (List.Tot.length l))
= array_group_zero_or_more_eq al l;
  match al l with
  | None -> ()
  | Some (l1, l2) ->
    List.Tot.append_length l1 l2;
    if Nil? l1
    then ()
    else begin
      let Some (l3, l4) = array_group_zero_or_more al l2 in
      let Some (l5, l6) = ar l4 in
      List.Tot.append_assoc l1 l3 l5;
      assert (array_group_concat (array_group_zero_or_more al) ar l == Some (List.Tot.append l1 (List.Tot.append l3 l5), l6));
      array_group_included_zero_or_more_l_aux al ar al' ar' l2;
      let Some (l3', l4') = array_group_zero_or_more al' l2 in
      let Some (l5', l6') = ar' l4' in
      List.Tot.append_assoc l1 l3' l5';
      ()
    end

let array_group_included_zero_or_more_l
  (#b: _)
  (al ar al' ar': array_group b)
: Lemma
  (requires (
    array_group_included al al' /\
    array_group_included ar (array_group_concat (array_group_zero_or_more al') ar')
  ))
  (ensures
    array_group_included (array_group_concat (array_group_zero_or_more al) ar) (array_group_concat (array_group_zero_or_more al') ar')
  )
= Classical.forall_intro (Classical.move_requires (array_group_included_zero_or_more_l_aux al ar al' ar'))

let array_group_included_choice_r_r
  (#b: _)
  (a1 a2l a2r a2q: array_group b)
: Lemma
  (requires (
    array_group_disjoint a1 a2l /\
    array_group_included a1 (array_group_concat a2r a2q)
  ))
  (ensures (
    array_group_included a1 (array_group_concat (array_group_choice a2l a2r) a2q)
  ))
= ()

// Recursive type (needed by COSE Section 5.1 "Recipient")

// Inspiring from Barthe et al., Type-Based Termination with Sized
// Products (CSL 2008): we allow recursion only at the level of
// destructors. In other words, instead of having a generic recursion
// combinator, we provide a recursion-enabled version only for each
// destructor combinator. We need to annotate it with a bound b (akin
// to the "size" annotation in a sized type.)

let rec t_array_rec
  (phi: (b: Cbor.cbor) -> (bounded_typ b -> array_group (Some b)))
  (w: Cbor.cbor)
: Tot bool
  (decreases w)
= let x = Cbor.unpack w in
  Cbor.CArray? x &&
  match_array_group (phi w (t_array_rec phi)) (Cbor.CArray?.v x)

let array_group_parser_spec_refinement
  (source: array_group None)
  (x: list Cbor.cbor)
: Tot prop
= match source x with
  | Some (_, []) -> True
  | _ -> False

let array_group_parser_spec_refinement_equiv
  (source: array_group None)
  (x: list Cbor.cbor)
: Lemma
  (ensures (array_group_parser_spec_refinement source x <==> source x == Some (x, [])))
  [SMTPat (array_group_parser_spec_refinement source x)]
= match source x with
  | Some (x', []) -> List.Tot.append_l_nil x'
  | _ -> ()

let array_group_parser_spec_arg
  (source: array_group None)
: Tot Type0
= (x: list Cbor.cbor {
    array_group_parser_spec_refinement source x
  })

let array_group_parser_spec_ret
  (source: array_group None)
  (#target: Type0)
  (target_size: target -> Tot nat)
  (target_prop: target -> bool)
  (x: array_group_parser_spec_arg source)
: Tot Type0
= (y: target { 
    target_size y == List.Tot.length x /\
    target_prop y
  })

let array_group_parser_spec
  (source: array_group None)
  (#target: Type0)
  (target_size: target -> Tot nat)
  (target_prop: target -> bool)
: Type0
= (x: array_group_parser_spec_arg source) -> Tot (array_group_parser_spec_ret source target_size target_prop x)

let array_group_serializer_spec
  (#source: array_group None)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: array_group_parser_spec source target_size target_prop)
: Type0
= (x: target { target_prop x }) -> Tot (y: array_group_parser_spec_arg source {
    p y == x
  })

noeq
type ag_spec
  (source: array_group None)
  (target: Type0)
  (inj: bool)
= {
  ag_size: target -> Tot nat;
  ag_serializable: target -> bool;
  ag_parser: array_group_parser_spec source ag_size ag_serializable;
  ag_serializer: array_group_serializer_spec ag_parser;
  ag_parser_inj: squash (inj ==> (forall (c: array_group_parser_spec_arg source) . ag_serializer (ag_parser c) == c));
}

let ag_spec_ext
  (#source1: array_group None)
  (#target: Type0)
  (#inj: bool)
  (spec1: ag_spec source1 target inj)
  (source2: array_group None {
    array_group_equiv source1 source2
  })
: Tot (ag_spec source2 target inj)
= {
  ag_size = spec1.ag_size;
  ag_serializable = spec1.ag_serializable;
  ag_parser = (fun (x: array_group_parser_spec_arg source2) -> spec1.ag_parser x);
  ag_serializer = (fun x -> spec1.ag_serializer x);
  ag_parser_inj = (spec1.ag_parser_inj; ());
}

let ag_spec_close_intro
  (#source1: array_group None)
  (#target: Type0)
  (#inj: bool)
  (spec1: ag_spec source1 target inj)
: Tot (ag_spec (close_array_group source1) target inj)
= {
  ag_size = spec1.ag_size;
  ag_serializable = spec1.ag_serializable;
  ag_parser = (fun (x: array_group_parser_spec_arg (close_array_group source1)) -> spec1.ag_parser x);
  ag_serializer = (fun x -> spec1.ag_serializer x);
  ag_parser_inj = (spec1.ag_parser_inj; ());
}

let ag_spec_close_elim
  (#source1: array_group None)
  (#target: Type0)
  (#inj: bool)
  (spec1: ag_spec (close_array_group source1) target inj)
: Tot (ag_spec source1 target inj)
= {
  ag_size = spec1.ag_size;
  ag_serializable = spec1.ag_serializable;
  ag_parser = (fun (x: array_group_parser_spec_arg source1) -> spec1.ag_parser x);
  ag_serializer = (fun x -> spec1.ag_serializer x);
  ag_parser_inj = (spec1.ag_parser_inj; ());
}

let ag_spec_maybe_close_intro
  (#source1: array_group None)
  (#target: Type0)
  (#inj: bool)
  (spec1: ag_spec source1 target inj)
  (close: bool)
: Tot (ag_spec (maybe_close_array_group source1 close) target inj)
= if close
  then ag_spec_close_intro spec1
  else spec1

let ag_spec_maybe_close_elim
  (#source1: array_group None)
  (#target: Type0)
  (#inj: bool)
  (#close: bool)
  (spec1: ag_spec (maybe_close_array_group source1 close) target inj)
: Tot (ag_spec source1 target inj)
= if close
  then ag_spec_close_elim spec1
  else spec1

let ag_spec_coerce_target_prop
  (#source: array_group None)
  (#target: Type0)
  (#inj: bool)
  (p: ag_spec source target inj)
  (target_size': target -> Tot nat {
    forall x . target_size' x == p.ag_size x
  })
  (target_prop': target -> bool {
    forall x . target_prop' x <==> p.ag_serializable x
  })
: ag_spec source target inj
= {
  ag_size = target_size';
  ag_serializable = target_prop';
  ag_parser = (p.ag_parser <: array_group_parser_spec source target_size' target_prop');
  ag_serializer = p.ag_serializer;
  ag_parser_inj = ();
}

let spec_array_group_serializable
  (#target: Type0)
  (target_size: target -> Tot nat)
  (target_prop: target -> bool)
  (x: target)
: Tot bool
= target_prop x &&
  target_size x < pow2 64

let parser_spec_array_group
  (#source: array_group None)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: array_group_parser_spec source target_size target_prop)
  (target_prop' : target -> bool {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64) // serializability condition
  })
: Tot (parser_spec (t_array source) target target_prop')
= fun x -> let Cbor.CArray a = Cbor.unpack x in p a

let serializer_spec_array_group
  (#source: array_group None)
  (#target: Type0)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p)
  (target_prop' : target -> bool {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64) // serializability condition
  })
: Tot (serializer_spec (parser_spec_array_group p target_prop'))
= fun x -> Cbor.pack (Cbor.CArray (s x))

let spec_array_group
  (#source: array_group None)
  (#target: Type0)
  (#inj: bool)
  (p: ag_spec source target inj)
: Tot (spec (t_array source) target inj)
= {
  serializable = spec_array_group_serializable p.ag_size p.ag_serializable;
  parser = parser_spec_array_group p.ag_parser _;
  serializer = serializer_spec_array_group p.ag_serializer _;
  parser_inj = ();
}

let ag_size_inj
  (#target1: Type0)
  (target1_size: (target1 -> nat))
  (#target2: Type0)
  (f21: (target2 -> target1))
  (x: target2)
: Tot nat
= target1_size (f21 x)

let array_group_parser_spec_inj
  (#source: array_group None)
  (#target1: Type0)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p: array_group_parser_spec source target_size1 target_prop1)
  (#target2: Type0)
  (f12: (target1 -> target2)) (f21: (target2 -> target1)) (prf_21_12: (x: target1) -> squash (f21 (f12 x) == x))
: Tot (array_group_parser_spec source (ag_size_inj target_size1 f21) (serializable_inj target_prop1 f21))
= fun c -> let x1 = p c in prf_21_12 x1; f12 x1

let array_group_serializer_spec_inj
  (#source: array_group None)
  (#target1: Type0)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p: array_group_parser_spec source target_size1 target_prop1)
  (s: array_group_serializer_spec p)
  (#target2: Type0)
  (f12: (target1 -> target2)) (f21: (target2 -> target1)) (prf_21_12: (x: target1) -> squash (f21 (f12 x) == x)) (prf_12_21: (x: target2) -> squash (f12 (f21 x) == x))
: Tot (array_group_serializer_spec (array_group_parser_spec_inj p f12 f21 prf_21_12))
= fun x2 -> prf_12_21 x2; s (f21 x2)

let ag_spec_inj_injective
  (#source:array_group None) (#target1 #target2: Type0) (#inj: bool)
  (s: ag_spec source target1 inj)
  (f12: (target1 -> target2)) (f21: (target2 -> target1)) (prf_21_12: (x: target1) -> squash (f21 (f12 x) == x)) (prf_12_21: (x: target2) -> squash (f12 (f21 x) == x))
  (c: array_group_parser_spec_arg source)
: Lemma
  (ensures (inj ==> array_group_serializer_spec_inj s.ag_serializer f12 f21 prf_21_12 prf_12_21 (array_group_parser_spec_inj s.ag_parser f12 f21 prf_21_12 c) == c))
= if inj
  then begin
    prf_21_12 (s.ag_parser c)
  end

let ag_spec_inj
  (#source:array_group None) (#target1 #target2: Type0) (#inj: bool)
  (s: ag_spec source target1 inj)
  (f12: (target1 -> target2)) (f21: (target2 -> target1)) (prf_21_12: (x: target1) -> squash (f21 (f12 x) == x)) (prf_12_21: (x: target2) -> squash (f12 (f21 x) == x))
: Tot (ag_spec source target2 inj)
= {
  ag_size = ag_size_inj s.ag_size f21;
  ag_serializable = serializable_inj s.ag_serializable f21;
  ag_parser = array_group_parser_spec_inj s.ag_parser f12 f21 prf_21_12;
  ag_serializer = array_group_serializer_spec_inj s.ag_serializer f12 f21 prf_21_12 prf_12_21;
  ag_parser_inj = Classical.forall_intro (ag_spec_inj_injective s f12 f21 prf_21_12 prf_12_21);
}

let array_group_parser_spec_bij
  (#source: array_group None)
  (#target1: Type0)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (f: array_group_parser_spec source target_size1 target_prop1)
  (#target2: Type0)
  (target_size2: target2 -> Tot nat)
  (target_prop2: target2 -> bool)
  (bij: bijection target1 target2 {
    (forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)) /\
    (forall x2 . target_prop2 x2 <==> target_prop1 (bij.bij_to_from x2))
  })
: Tot (array_group_parser_spec source target_size2 target_prop2)
= fun x -> bij.bij_from_to (f x)

let array_group_serializer_spec_bij
  (#source: array_group None)
  (#target1: Type0)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#f: array_group_parser_spec source target_size1 target_prop1)
  (s: array_group_serializer_spec f)
  (#target2: Type0)
  (target_size2: target2 -> Tot nat)
  (target_prop2: target2 -> bool)
  (bij: bijection target1 target2 {
    (forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)) /\
    (forall x2 . target_prop2 x2 <==> target_prop1 (bij.bij_to_from x2))
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_bij f target_size2 target_prop2 bij))
= fun x -> s (bij.bij_to_from x)

let ag_spec_bij_size
  (#source: array_group None)
  (#target1: Type0)
  (#inj1: bool)
  (f: ag_spec source target1 inj1)
  (#target2: Type0)
  (bij: bijection target1 target2)
  (x2: target2)
: Tot nat
= f.ag_size (bij.bij_to_from x2)

let ag_spec_bij_serializable
  (#source: array_group None)
  (#target1: Type0)
  (#inj1: bool)
  (f: ag_spec source target1 inj1)
  (#target2: Type0)
  (bij: bijection target1 target2)
  (x2: target2)
: Tot bool
= f.ag_serializable (bij.bij_to_from x2)

let ag_spec_bij
  (#source: array_group None)
  (#target1: Type0)
  (#inj1: bool)
  (f: ag_spec source target1 inj1)
  (#target2: Type0)
  (bij: bijection target1 target2)
: Tot (ag_spec source target2 inj1)
= {
  ag_size = ag_spec_bij_size f bij;
  ag_serializable = ag_spec_bij_serializable f bij;
  ag_parser = array_group_parser_spec_bij f.ag_parser _ _ bij;
  ag_serializer = array_group_serializer_spec_bij f.ag_serializer _ _ bij;
  ag_parser_inj = ();
}

let array_group_parser_spec_item
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> Tot bool)
  (p: parser_spec ty target target_prop)
  (target_size: target -> Tot nat {
    forall x . target_size x == 1
  })
: Tot (array_group_parser_spec (array_group_item ty) target_size target_prop)
= fun x -> let [hd] = x in p hd

val array_group_serializer_spec_item
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> bool)
  (#p: parser_spec ty target target_prop)
  (s: serializer_spec p)
  (target_size: target -> Tot nat {
    forall x . target_size x == 1
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_item p target_size))

val array_group_serializer_spec_item_eq
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> bool)
  (#p: parser_spec ty target target_prop)
  (s: serializer_spec p)
  (target_size: target -> Tot nat {
    forall x . target_size x == 1
  })
  (x: target { target_prop x })
: Lemma
  (ensures (array_group_serializer_spec_item s target_size x == [s x]))
  [SMTPat (array_group_serializer_spec_item s target_size x)]

let ag_spec_item_size
  (target: Type)
  (x: target)
: Tot nat
= 1

let ag_spec_item
  (#ty: typ)
  (#target: Type)
  (#inj: bool)
  (p: spec ty target inj)
: Tot (ag_spec (array_group_item ty) target inj)
= {
  ag_size = ag_spec_item_size target;
  ag_serializable = p.serializable;
  ag_parser = array_group_parser_spec_item p.parser _;
  ag_serializer = array_group_serializer_spec_item p.serializer _;
  ag_parser_inj = ();
}

val array_group_parser_spec_concat
  (#source1: array_group None)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p1: array_group_parser_spec source1 target_size1 target_prop1)
  (#source2: array_group None)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (p2: array_group_parser_spec source2 target_size2 target_prop2 {
    array_group_concat_unique_weak source1 source2
  })
  (target_size: (target1 & target2) -> Tot nat {
    forall x . target_size x == target_size1 (fst x) + target_size2 (snd x)
  })
  (target_prop: (target1 & target2) -> bool {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
: Tot (array_group_parser_spec (array_group_concat source1 source2) target_size target_prop)

#restart-solver

val array_group_parser_spec_concat_eq
  (#source1: array_group None)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p1: array_group_parser_spec source1 target_size1 target_prop1)
  (#source2: array_group None)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (p2: array_group_parser_spec source2 target_size2 target_prop2 {
    array_group_concat_unique_weak source1 source2
  })
  (target_size: (target1 & target2) -> Tot nat {
    forall x . target_size x == target_size1 (fst x) + target_size2 (snd x)
  })
  (target_prop: (target1 & target2) -> bool {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
  (x: array_group_parser_spec_arg (array_group_concat source1 source2))
: Lemma
  (let Some (x1, x2) = source1 x in
    source1 x1 == Some (x1, []) /\
    array_group_parser_spec_concat p1 p2 target_size target_prop x == (
    (p1 x1, p2 x2)
  ))
  [SMTPat (array_group_parser_spec_concat p1 p2 target_size target_prop x)]

let array_group_serializer_spec_concat
  (#source1: array_group None)
  (#target1: Type)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p1: array_group_parser_spec source1 target_size1 target_prop1)
  (s1: array_group_serializer_spec p1)
  (#source2: array_group None)
  (#target2: Type)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (#p2: array_group_parser_spec source2 target_size2 target_prop2)
  (s2: array_group_serializer_spec p2 {
    array_group_concat_unique_weak source1 source2
  })
  (target_size: (target1 & target2) -> Tot nat {
    forall x . target_size x == target_size1 (fst x) + target_size2 (snd x)
  })
  (target_prop: (target1 & target2) -> bool {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_concat p1 p2 target_size target_prop))
= fun x ->
    let (x1, x2) = x in
    let l1 = s1 x1 in
    let l2 = s2 x2 in
    let res = l1 `List.Tot.append` l2 in
    array_group_concat_unique_weak_elim2 source1 source2 l1 l2;
    res

let ag_spec_concat_size
  (#target1: Type)
  (p1: target1 -> nat)
  (#target2: Type)
  (p2: target2 -> nat)
  (x: (target1 & target2))
: Tot nat
= p1 (fst x) + p2 (snd x)

let ag_spec_concat_serializable
  (#target1: Type)
  (p1: target1 -> bool)
  (#target2: Type)
  (p2: target2 -> bool)
  (x: (target1 & target2))
: Tot bool
= p1 (fst x) && p2 (snd x)

let ag_spec_concat
  (#source1: array_group None)
  (#target1: Type)
  (#inj1: bool)
  (p1: ag_spec source1 target1 inj1)
  (#source2: array_group None)
  (#target2: Type)
  (#inj2: bool)
  (p2: ag_spec source2 target2 inj2 {
    array_group_concat_unique_weak source1 source2
  })
: Tot (ag_spec (array_group_concat source1 source2) (target1 & target2) (inj1 && inj2))
= {
  ag_size = ag_spec_concat_size p1.ag_size p2.ag_size;
  ag_serializable = ag_spec_concat_serializable p1.ag_serializable p2.ag_serializable;
  ag_parser = array_group_parser_spec_concat p1.ag_parser p2.ag_parser _ _;
  ag_serializer = array_group_serializer_spec_concat p1.ag_serializer p2.ag_serializer _ _;
  ag_parser_inj = ();
}

let rec array_group_parser_spec_zero_or_more'
  (#source: array_group None)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: array_group_parser_spec source target_size target_prop {
    array_group_concat_unique_strong source source
  })
  (target_size' : list target -> Tot nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (target_prop' : list target -> bool {
    forall x . target_prop' x <==> (forall y . List.Tot.memP y x ==> target_prop y)
  })
  (x: array_group_parser_spec_arg (array_group_zero_or_more source))
: Tot (array_group_parser_spec_ret (array_group_zero_or_more source) target_size' target_prop' x)
  (decreases (List.Tot.length x))
= match source x with
  | None ->
    assert (x == []);
    let res : list target = [] in
    assert (Nil? res);
    assert (target_size' res == 0);
    res
  | Some (l1, l2) ->
    if Nil? l1
    then []
    else begin
      array_group_concat_unique_weak_zero_or_more_right source source;
      List.Tot.append_length l1 l2;
      let q = array_group_parser_spec_zero_or_more' p target_size' target_prop' l2 in
      p l1 :: q
    end

let array_group_parser_spec_zero_or_more
  (#source: array_group None)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: array_group_parser_spec source target_size target_prop {
    array_group_concat_unique_strong source source
  })
  (target_size' : list target -> Tot nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (target_prop' : list target -> bool {
    forall x . target_prop' x <==> (forall y . List.Tot.memP y x ==> target_prop y)
  })
: Tot (array_group_parser_spec (array_group_zero_or_more source) target_size' target_prop')
= array_group_parser_spec_zero_or_more' p target_size' target_prop'

let array_group_is_nonempty (a: array_group None) : Tot prop =
    forall l . match a l with
    | Some (consumed, _) -> Cons? consumed
    | _ -> True

let nonempty_array_group : Type0 =
  (a: array_group None { array_group_is_nonempty a })

#push-options "--z3rlimit 16"

let rec array_group_serializer_spec_zero_or_more'
  (#source: nonempty_array_group)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p {
    array_group_concat_unique_strong source source
  })
  (target_size' : list target -> Tot nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (target_prop' : list target -> bool {
    forall x . target_prop' x <==> (forall y . List.Tot.memP y x ==> target_prop y)
  })
  (x: list target { target_prop' x })
: Tot (y: array_group_parser_spec_arg (array_group_zero_or_more source) {
    array_group_parser_spec_zero_or_more p target_size' target_prop' y == x
  })
  (decreases x)
= match x with
  | [] ->
    assert (source [] == None);
    []
  | a :: q ->
    array_group_concat_unique_weak_zero_or_more_right source source;
    let l1 = s a in
    let l2 = array_group_serializer_spec_zero_or_more' s target_size' target_prop' q in
    let res = l1 `List.Tot.append` l2 in
    res

#pop-options

let array_group_serializer_spec_zero_or_more
  (#source: nonempty_array_group)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p {
    array_group_concat_unique_strong source source
  })
  (target_size' : list target -> Tot nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (target_prop' : list target -> bool {
    forall x . target_prop' x <==> (forall y . List.Tot.memP y x ==> target_prop y)
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_zero_or_more p target_size' target_prop'))
= array_group_serializer_spec_zero_or_more' s target_size' target_prop'

let rec ag_spec_zero_or_more_size
  (#target: Type)
  (p: target -> nat)
  (l: list target)
: Tot nat
  (decreases l)
= match l with
  | [] -> 0
  | hd :: tl -> p hd + ag_spec_zero_or_more_size p tl

let ag_spec_zero_or_more_serializable
  (#target: Type)
  (p: target -> bool)
  (x: list target)
: Tot bool
= List.Tot.for_all p x

let ag_spec_zero_or_more_serializable_equiv
  (#target: Type)
  (p: target -> bool)
  (x: list target)
: Lemma
  (ensures (ag_spec_zero_or_more_serializable p x <==>
    (forall y . List.Tot.memP y x ==> p y)
  ))
  [SMTPat (ag_spec_zero_or_more_serializable p x)]
= List.Tot.for_all_mem p x

let rec ag_spec_zero_or_more_inj
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (p: ag_spec source target inj {
    array_group_concat_unique_strong source source
  })
  (c: array_group_parser_spec_arg (array_group_zero_or_more source))
: Lemma
  (requires inj)
  (ensures (array_group_serializer_spec_zero_or_more p.ag_serializer (ag_spec_zero_or_more_size p.ag_size) (ag_spec_zero_or_more_serializable p.ag_serializable) (array_group_parser_spec_zero_or_more p.ag_parser (ag_spec_zero_or_more_size p.ag_size) (ag_spec_zero_or_more_serializable p.ag_serializable) c) == c))
  (decreases (List.Tot.length c))
= match source c with
  | None -> ()
  | Some (l1, l2) ->
    if Nil? l1
    then ()
    else begin
      array_group_concat_unique_weak_zero_or_more_right source source;
      List.Tot.append_length l1 l2;
      ag_spec_zero_or_more_inj p l2
    end

let array_group_parser_spec_zero_or_more0
  (#source: array_group None)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: array_group_parser_spec source target_size target_prop)
  (sq: squash (
    array_group_concat_unique_strong source source
  ))
: Tot (array_group_parser_spec (array_group_zero_or_more source) (ag_spec_zero_or_more_size target_size) (ag_spec_zero_or_more_serializable target_prop))
= array_group_parser_spec_zero_or_more p _ _

let ag_spec_zero_or_more
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (p: ag_spec source target inj {
    array_group_concat_unique_strong source source
  })
: Tot (ag_spec (array_group_zero_or_more source) (list target) inj)
= {
  ag_size = ag_spec_zero_or_more_size p.ag_size;
  ag_serializable = ag_spec_zero_or_more_serializable p.ag_serializable;
  ag_parser = array_group_parser_spec_zero_or_more0 p.ag_parser ();
  ag_serializer = array_group_serializer_spec_zero_or_more p.ag_serializer _ _;
  ag_parser_inj = Classical.forall_intro (Classical.move_requires (ag_spec_zero_or_more_inj p));
}

let array_group_parser_spec_one_or_more
  (#source: array_group None)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: array_group_parser_spec source target_size target_prop {
    array_group_concat_unique_strong source source
  })
  (target_size1 : list target -> Tot nat {
    forall (l: list target) . target_size1 l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size1 (List.Tot.tl l))
  })
  (target_prop1 : list target -> bool {
    forall x . target_prop1 x <==> (Cons? x /\ (forall y . List.Tot.memP y x ==> target_prop y))
  })
  (target_prop1' : list target -> bool {
    forall x . target_prop1' x <==> (Nil? x || target_prop1 x)
  })
: Tot (array_group_parser_spec (array_group_one_or_more source) target_size1 target_prop1)
= fun x ->
  array_group_concat_unique_weak_zero_or_more_right source source;
  let Some (l1, l2) = source x in
  List.Tot.append_length l1 l2;
  p l1 :: array_group_parser_spec_zero_or_more p target_size1 target_prop1' l2

let ag_spec_one_or_more_serializable
  (#target: Type)
  (p: target -> bool)
  (x: list target)
: Tot bool
= Cons? x &&
  ag_spec_zero_or_more_serializable p x

let array_group_parser_spec_one_or_more0
  (#source: array_group None)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: array_group_parser_spec source target_size target_prop)
  (sq: squash (
    array_group_concat_unique_strong source source
  ))
: Tot (array_group_parser_spec (array_group_one_or_more source) (ag_spec_zero_or_more_size target_size) (ag_spec_one_or_more_serializable target_prop))
= array_group_parser_spec_one_or_more p _ _ (ag_spec_zero_or_more_serializable target_prop)

let array_group_serializer_spec_one_or_more
  (#source: nonempty_array_group)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p {
    array_group_concat_unique_strong source source
  })
  (target_size1 : list target -> Tot nat {
    forall (l: list target) . target_size1 l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size1 (List.Tot.tl l))
  })
  (target_prop1 : list target -> bool {
    forall x . target_prop1 x <==> (Cons? x /\ (forall y . List.Tot.memP y x ==> target_prop y))
  })
  (target_prop1' : list target -> bool {
    forall x . target_prop1' x <==> (Nil? x || target_prop1 x)
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_one_or_more p target_size1 target_prop1 target_prop1'))
= fun x ->
  array_group_concat_unique_weak_zero_or_more_right source source;
  let hd :: tl = x in
  let l1 = s hd in
  let l2 = array_group_serializer_spec_zero_or_more s target_size1 target_prop1' tl in
  List.Tot.append_length l1 l2;
  l1 `List.Tot.append` l2

let ag_spec_one_or_more_inj
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (p: ag_spec source target inj {
    array_group_concat_unique_strong source source
  })
  (c: array_group_parser_spec_arg (array_group_one_or_more source))
: Lemma
  (requires inj)
  (ensures (array_group_serializer_spec_one_or_more p.ag_serializer (ag_spec_zero_or_more_size p.ag_size) (ag_spec_one_or_more_serializable p.ag_serializable) (ag_spec_zero_or_more_serializable p.ag_serializable) (array_group_parser_spec_one_or_more p.ag_parser (ag_spec_zero_or_more_size p.ag_size) (ag_spec_one_or_more_serializable p.ag_serializable) (ag_spec_zero_or_more_serializable p.ag_serializable) c) == c))
= Classical.forall_intro (Classical.move_requires (ag_spec_zero_or_more_inj p));
  array_group_concat_unique_weak_zero_or_more_right source source;
  let (x1, x2) = (ag_spec_concat p (ag_spec_zero_or_more p)).ag_parser c in
  assert (array_group_parser_spec_one_or_more p.ag_parser (ag_spec_zero_or_more_size p.ag_size) (ag_spec_one_or_more_serializable p.ag_serializable) (ag_spec_zero_or_more_serializable p.ag_serializable) c == x1 :: x2)

let ag_spec_one_or_more
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (p: ag_spec source target inj {
    array_group_concat_unique_strong source source
  })
: Tot (ag_spec (array_group_one_or_more source) (list target) inj)
= {
  ag_size = ag_spec_zero_or_more_size p.ag_size;
  ag_serializable = ag_spec_one_or_more_serializable p.ag_serializable;
  ag_parser = array_group_parser_spec_one_or_more0 p.ag_parser ();
  ag_serializer = array_group_serializer_spec_one_or_more p.ag_serializer _ _ (ag_spec_zero_or_more_serializable p.ag_serializable);
  ag_parser_inj = Classical.forall_intro (Classical.move_requires (ag_spec_one_or_more_inj p));
}

let array_group_parser_spec_choice
  (#source1: array_group None)
  (#target1: Type0)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (p1: array_group_parser_spec source1 target_size1 target_prop1)
  (#source2: array_group None)
  (#target2: Type0)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (p2: array_group_parser_spec source2 target_size2 target_prop2)
  (target_size: (target1 `either` target2) -> Tot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> bool {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })
: Tot (array_group_parser_spec (source1 `array_group_choice` source2) target_size target_prop)
= fun x ->
    if Some? (source1 x)
    then Inl (p1 x)
    else Inr (p2 x)

let array_group_serializer_spec_choice
  (#source1: array_group None)
  (#target1: Type0)
  (#target_size1: target1 -> Tot nat)
  (#target_prop1: target1 -> bool)
  (#p1: array_group_parser_spec source1 target_size1 target_prop1)
  (s1: array_group_serializer_spec p1)
  (#source2: array_group None)
  (#target2: Type0)
  (#target_size2: target2 -> Tot nat)
  (#target_prop2: target2 -> bool)
  (#p2: array_group_parser_spec source2 target_size2 target_prop2)
  (s2: array_group_serializer_spec p2 { source1 `array_group_disjoint` source2 }) // disjointness needed to avoid the CBOR object serialized from one case to be parsed into the other case
  (target_size: (target1 `either` target2) -> Tot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> bool {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_choice p1 p2 target_size target_prop))
= fun x -> match x with
  | Inl y -> s1 y
  | Inr y -> s2 y

let ag_spec_choice_size
  (#target1: Type0)
  (p1: target1 -> nat)
  (#target2: Type0)
  (p2: target2 -> nat)
  (x: either target1 target2)
: Tot nat
= match x with
  | Inl x1 -> p1 x1
  | Inr x2 -> p2 x2

let ag_spec_choice_serializable
  (#target1: Type0)
  (p1: target1 -> bool)
  (#target2: Type0)
  (p2: target2 -> bool)
  (x: either target1 target2)
: Tot bool
= match x with
  | Inl x1 -> p1 x1
  | Inr x2 -> p2 x2

let ag_spec_choice
  (#source1: array_group None)
  (#target1: Type0)
  (#inj1: bool)
  (p1: ag_spec source1 target1 inj1)
  (#source2: array_group None)
  (#target2: Type0)
  (#inj2: bool)
  (p2: ag_spec source2 target2 inj2 { source1 `array_group_disjoint` source2 })
: Tot (ag_spec (source1 `array_group_choice` source2) (either target1 target2) (inj1 && inj2))
= {
  ag_size = ag_spec_choice_size p1.ag_size p2.ag_size;
  ag_serializable = ag_spec_choice_serializable p1.ag_serializable p2.ag_serializable;
  ag_parser = array_group_parser_spec_choice p1.ag_parser p2.ag_parser _ _;
  ag_serializer = array_group_serializer_spec_choice p1.ag_serializer p2.ag_serializer _ _;
  ag_parser_inj = ();
}

let ag_spec_choice'
  (#source1: array_group None)
  (#target1: Type0)
  (#inj1: bool)
  (p1: ag_spec source1 target1 inj1)
  (#source2: array_group None)
  (#target2: Type0)
  (#inj2: bool)
  (p2: ag_spec source2 target2 inj2 { source1 `array_group_disjoint` close_array_group source2 })
: Tot (ag_spec (source1 `array_group_choice` source2) (either target1 target2) (inj1 && inj2))
=
    ag_spec_close_elim
      (ag_spec_ext
        (ag_spec_close_intro
          (ag_spec_choice
            p1
            (ag_spec_close_intro
              p2
            )
          )
        )
        (close_array_group (array_group_choice source1 source2))
      )

let array_group_parser_spec_zero_or_one
  (#source: array_group None)
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (p: array_group_parser_spec source target_size target_prop)
  (target_size': option target -> Tot nat {
    forall x . target_size' x == begin match x with
    | None -> 0
    | Some x -> target_size x
    end
  })
  (target_prop': option target -> bool {
    forall x . target_prop' x <==> begin match x with
    | None -> True
    | Some x -> target_prop x
    end
  })
: Tot (array_group_parser_spec (array_group_zero_or_one source) target_size' target_prop')
= fun x ->
    if Some? (source x)
    then Some (p x)
    else None

let array_group_serializer_spec_zero_or_one
  (#source: nonempty_array_group) // needed because the empty case must map to None only
  (#target: Type)
  (#target_size: target -> Tot nat)
  (#target_prop: target -> bool)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p)
  (target_size': option target -> Tot nat {
    forall x . target_size' x == begin match x with
    | None -> 0
    | Some x -> target_size x
    end
  })
  (target_prop': option target -> bool {
    forall x . target_prop' x <==> begin match x with
    | None -> True
    | Some x -> target_prop x
    end
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_zero_or_one p target_size' target_prop'))
= fun x ->
    match x with
    | None -> []
    | Some y -> s y

let ag_spec_zero_or_one_size
  (#target: Type)
  (p: target -> nat)
  (x: option target)
: Tot nat
= match x with
  | None -> 0
  | Some x' -> p x'

let ag_spec_zero_or_one_serializable
  (#target: Type)
  (p: target -> bool)
  (x: option target)
: Tot bool
= match x with
  | None -> true
  | Some x' -> p x'

let ag_spec_zero_or_one
  (#source: nonempty_array_group)
  (#target: Type)
  (#inj: bool)
  (p: ag_spec source target inj)
: Tot (ag_spec (array_group_zero_or_one source) (option target) inj)
= {
  ag_size = ag_spec_zero_or_one_size p.ag_size;
  ag_serializable = ag_spec_zero_or_one_serializable p.ag_serializable;
  ag_parser = array_group_parser_spec_zero_or_one p.ag_parser _ _;
  ag_serializer = array_group_serializer_spec_zero_or_one p.ag_serializer _ _;
  ag_parser_inj = ();
}
