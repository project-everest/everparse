module CDDL.Spec.ArrayGroup
include CDDL.Spec.Base
module Cbor = CBOR.Spec
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

module Pull = FStar.Ghost.Pull

noextract
let opt_precedes_list
  (#t1 #t2: Type)
  (l: list t1)
  (b: option t2)
: Tot prop
= List.Tot.for_all (Pull.pull (opt_precedes_list_item b)) l

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

[@@erasable; noextract_to "krml"]
let array_group3 (bound: option Cbor.raw_data_item) = (l: list Cbor.raw_data_item { opt_precedes_list l bound }) -> Ghost (option (list Cbor.raw_data_item & list Cbor.raw_data_item))
  (requires True)
  (ensures (fun l' -> match l' with
  | None -> True
  | Some (l1, l2) -> l == l1 `List.Tot.append` l2
  ))

noextract
let array_group3_equiv
  #b
  (g1 g2: array_group3 b)
: Tot prop
= forall l . g1 l == g2 l

let array_group3_always_false #b : array_group3 b = fun _ -> None

let opt_precedes_list_assoc
  (#t1 #t2: Type)
  (l1 l2: list t1)
  (b: option t2)
: Lemma
  (opt_precedes_list (l1 `List.Tot.append` l2) b <==>  opt_precedes_list l1 b /\ opt_precedes_list l2 b)
  [SMTPat (opt_precedes_list (l1 `List.Tot.append` l2) b)]
= List.Tot.for_all_append (Pull.pull (opt_precedes_list_item b)) l1 l2

let array_group3_empty #b : array_group3 b = fun x -> Some ([], x)
let array_group3_concat #b (a1 a3: array_group3 b) : array_group3 b =
  (fun l ->
    match a1 l with
    | None -> None
    | Some (l1, l2) ->  begin match a3 l2 with
      | None -> None
      | Some (l3, l4) -> List.Tot.append_assoc l1 l3 l4; Some (List.Tot.append l1 l3, l4)
    end
  )

let array_group3_concat_equiv
  #b
  (a1 a1' a2 a2' : array_group3 b)
: Lemma
  (requires ((a1 `array_group3_equiv` a1') /\ (a2 `array_group3_equiv` a2')))
  (ensures ((a1 `array_group3_concat` a2) `array_group3_equiv` (a1' `array_group3_concat` a2')))
= ()

val array_group3_concat_assoc
  (#b: _)
  (a1 a2 a3: array_group3 b)
: Lemma
  (array_group3_concat a1 (array_group3_concat a2 a3) `array_group3_equiv`
    array_group3_concat (array_group3_concat a1 a2) a3)
  [SMTPatOr [
//    [SMTPat (array_group3_concat a1 (array_group3_concat a2 a3))];
    [SMTPat (array_group3_concat (array_group3_concat a1 a2) a3)]
  ]]

let array_group3_concat_unique_strong
  #b (a1 a3: array_group3 b)
: Tot prop
= (forall (l: (l: list Cbor.raw_data_item { opt_precedes_list l b })) (l' rem: list Cbor.raw_data_item) .
    array_group3_concat a1 a3 l == Some (l', rem) <==> (
      (exists (l1 l2 l3: list Cbor.raw_data_item) .
        l == l1 `List.Tot.append` l2 /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l3, rem) /\
        l' == l1 `List.Tot.append` l3
  ))) /\
  (forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) /\ Some? (a3 l2)) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
  )

let array_group3_concat_unique_strong_equiv
  #b (a1 a1' a3 a3': array_group3 b)
: Lemma
  (requires (
    array_group3_equiv a1 a1' /\
    array_group3_equiv a3 a3'
  ))
  (ensures (
    array_group3_concat_unique_strong a1 a3 <==>
    array_group3_concat_unique_strong a1' a3'
  ))
= array_group3_concat_equiv a1 a1' a3 a3'

let array_group3_strong_prefix
  #b (a1: array_group3 b)
: Tot prop
= forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) <==> a1 (l1 `List.Tot.append` l2) == Some (l1, l2))

val array_group3_concat_unique_strong_strong_prefix
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a2 /\
    array_group3_strong_prefix a2
  ))
  (ensures (
    array_group3_strong_prefix (array_group3_concat a1 a2)
  ))

let array_group3_choice #b (a1 a3: array_group3 b) : array_group3 b =
  fun l -> match a1 l with
    | None -> a3 l
    | Some l3 -> Some l3

let array_group3_disjoint #b (a1 a2: array_group3 b) : Tot prop
= (forall (l: list Cbor.raw_data_item { opt_precedes_list l b }) . ~ (Some? (a1 l) /\ Some? (a2 l)))

val array_group3_concat_unique_strong_choice_left #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (
    array_group3_concat_unique_strong a1 a3 /\
    array_group3_concat_unique_strong a2 a3 /\
    array_group3_disjoint a1 a2
  ))
  (ensures (
    array_group3_concat_unique_strong (array_group3_choice a1 a2) a3
  ))

let rec array_group3_zero_or_more' #b (a: array_group3 b) (l: list Cbor.raw_data_item { opt_precedes_list l b }) : Ghost (option (list Cbor.raw_data_item & list Cbor.raw_data_item))
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
      begin match array_group3_zero_or_more' a l2 with
      | None -> None
      | Some (l2', l3) -> List.Tot.append_assoc l1 l2' l3; Some (List.Tot.append l1 l2', l3)
      end

let array_group3_zero_or_more #b : array_group3 b -> array_group3 b = array_group3_zero_or_more'

val array_group3_zero_or_more_some
  (#b: _)
  (a: array_group3 b)
  (l: list Cbor.raw_data_item { opt_precedes_list l b })
: Lemma
  (ensures (Some? (array_group3_zero_or_more a l)))
  [SMTPat (array_group3_zero_or_more a l)]

val array_group3_zero_or_more_equiv (#b: _)
 (a1 a2: array_group3 b)
: Lemma
  (requires array_group3_equiv a1 a2)
  (ensures array_group3_equiv (array_group3_zero_or_more a1) (array_group3_zero_or_more a2))
  [SMTPat (array_group3_equiv (array_group3_zero_or_more a1) (array_group3_zero_or_more a2))]

val array_group3_concat_unique_strong_zero_or_more_left
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong a1 a1 /\
    array_group3_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group3_concat_unique_strong (array_group3_zero_or_more a1) a2
  ))

let array_group3_concat_unique_weak
  #b (a1 a3: array_group3 b)
: Tot prop
= (forall (l: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
    array_group3_concat a1 a3 l == Some (l, []) ==> (
      (exists (l1 l2: list Cbor.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
  ))) /\
  (forall (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) .
    (a1 l1 == Some (l1, []) /\ a3 l2 == Some (l2, [])) ==>
    a1 (l1 `List.Tot.append` l2) == Some (l1, l2)
  )

let array_group3_concat_unique_weak_elim2
  #b (a1 a3: array_group3 b)
  (l1 l2: (l: list Cbor.raw_data_item { opt_precedes_list l b }))
: Lemma
  (requires (
    array_group3_concat_unique_weak a1 a3 /\
    a1 l1 == Some (l1, []) /\
    a3 l2 == Some (l2, [])
  ))
  (ensures a1 (l1 `List.Tot.append` l2) == Some (l1, l2))
= ()

val array_group3_concat_unique_weak_intro
  (#b: _) (a1 a3: array_group3 b)
  (prf1:
    (l: (l: list Cbor.raw_data_item { opt_precedes_list l b })) ->
    Lemma
    (requires array_group3_concat a1 a3 l == Some (l, []))
    (ensures
      (exists (l1 l2: list Cbor.raw_data_item) .
        a1 l == Some (l1, l2) /\
        a1 l1 == Some (l1, []) /\
        a3 l2 == Some (l2, [])
    ))
//    [SMTPat (array_group3_concat a1 a3 l)]
  )
  (prf2:
    (l1: (l: list Cbor.raw_data_item { opt_precedes_list l b })) ->
    (l2: (l: list Cbor.raw_data_item { opt_precedes_list l b })) ->
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
  (array_group3_concat_unique_weak a1 a3)

let list_append_l_nil
  (#t: Type)
  (l: list t)
: Lemma
  (l `List.Tot.append` [] == l)
  [SMTPat (l `List.Tot.append` [])]
= List.Tot.append_l_nil l

val array_group3_concat_unique_weak_zero_or_more_left
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong a1 a1 /\
    array_group3_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_zero_or_more a1) a2
  ))

val array_group3_concat_unique_weak_zero_or_more_right
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak a1 (array_group3_zero_or_more a2)
  ))

val array_group3_concat_unique_weak_zero_or_more
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_concat_unique_strong a1 a1 /\
    array_group3_concat_unique_strong a1 a2 /\
    array_group3_disjoint a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_zero_or_more a1) (array_group3_zero_or_more a2)
  ))

val array_group3_concat_unique_weak_choice_right #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (
    array_group3_concat_unique_weak a1 a2 /\
    array_group3_concat_unique_weak a1 a3
  ))
  (ensures (
    array_group3_concat_unique_weak a1 (array_group3_choice a2 a3)
  ))

val array_group3_concat_unique_weak_choice_left #b (a1 a2 a3: array_group3 b) : Lemma
  (requires (
    array_group3_concat_unique_weak a1 a3 /\
    array_group3_concat_unique_weak a2 a3 /\
    array_group3_disjoint a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_choice a1 a2) a3
  ))

#restart-solver
let array_group_concat_unique_weak_concat_left
  (g1 g2 g3: array_group3 None)
: Lemma
  (requires
    array_group3_concat_unique_weak g1 g2 /\
    array_group3_concat_unique_weak g2 g3 /\    
    array_group3_concat_unique_weak g1 (g2 `array_group3_concat` g3)
  )
  (ensures
    array_group3_concat_unique_weak (g1 `array_group3_concat` g2) g3
  )
=   let a1 = g1 `array_group3_concat` g2 in
    let a3 = g3 in
    array_group3_concat_unique_weak_intro a1 a3
      (fun l -> ())
      (fun l1 l2 ->
        let Some (l1l, l1r) = g1 l1 in
        List.Tot.append_assoc l1l l1r l2
      );
    assert (array_group3_concat_unique_weak a1 a3)

let array_group3_one_or_more #b (a: array_group3 b) : array_group3 b =
  a `array_group3_concat` array_group3_zero_or_more a

let array_group3_one_or_more_equiv #b
 (a1 a2: array_group3 b)
: Lemma
  (requires array_group3_equiv a1 a2)
  (ensures array_group3_equiv (array_group3_one_or_more a1) (array_group3_one_or_more a2))
  [SMTPat (array_group3_equiv (array_group3_one_or_more a1) (array_group3_one_or_more a2))]
= array_group3_zero_or_more_equiv a1 a2

let array_group3_zero_or_one #b (a: array_group3 b) : Tot (array_group3 b) =
  a `array_group3_choice` array_group3_empty

val array_group3_concat_unique_strong_concat_left
  (#b: _)
  (g1 g2 g3: array_group3 b)
: Lemma
  (requires
    array_group3_concat_unique_strong g1 (array_group3_concat g2 g3) /\
    array_group3_concat_unique_strong g2 g3 /\
    array_group3_concat_unique_weak g1 g2
  )
  (ensures
    array_group3_concat_unique_strong (array_group3_concat g1 g2) g3
  )

val array_group3_concat_unique_strong_zero_or_one_left
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group3_concat_unique_strong (array_group3_zero_or_one a1) a2
  ))

val array_group3_concat_unique_strong_one_or_more_left
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong a1 a1 /\
    array_group3_concat_unique_strong a1 a2
  ))
  (ensures (
    array_group3_concat_unique_strong (array_group3_one_or_more a1) a2
  ))

val array_group3_concat_unique_weak_zero_or_one_left
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_zero_or_one a1) a2
  ))

val array_group3_concat_unique_weak_one_or_more_left
  (#b: _) (a1 a2: array_group3 b)
: Lemma
  (requires (
    array_group3_disjoint a1 a2 /\
    array_group3_concat_unique_strong a1 a1 /\
    array_group3_concat_unique_weak a1 a2
  ))
  (ensures (
    array_group3_concat_unique_weak (array_group3_one_or_more a1) a2
  ))

let array_group3_item (#b: option Cbor.raw_data_item) (t: bounded_typ_gen b) : array_group3 b = fun l ->
  match l with
  | [] -> None
  | a :: q -> if t a then Some ([a], q) else None

let array_group3_item_equiv
  #b
  (t1 t2: bounded_typ_gen b)
: Lemma
  (requires (t1 `typ_equiv` t2))
  (ensures (array_group3_item t1 `array_group3_equiv` array_group3_item t2))
= ()

let match_array_group3 (#b: option Cbor.raw_data_item) (a: array_group3 b)
  (l: list Cbor.raw_data_item {opt_precedes_list l b})
: GTot bool
= match a l with
  | Some (_, l') -> Nil? l'
  | _ -> false

let t_array3 (#b: option Cbor.raw_data_item) (a: array_group3 b) : bounded_typ_gen b = fun x ->
  Cbor.Array? x &&
  match_array_group3 a (Cbor.Array?.v x)

let t_array3_equiv
  #b
  (a1 a2: array_group3 b)
: Lemma
  (requires (array_group3_equiv a1 a2))
  (ensures (typ_equiv (t_array3 a1) (t_array3 a2)))
= ()

let close_array_group
  (#b: _)
  (t: array_group3 b)
: Tot (array_group3 b)
= fun l ->
    let res = t l in
    match res with
    | Some (_, []) -> res
    | _ -> None

let maybe_close_array_group
  (#b: _)
  (t: array_group3 b)
  (close: bool)
: Tot (array_group3 b)
= if close
  then close_array_group t
  else t

let array3_close_array_group
  (#b: _)
  (a: array_group3 b)
: Lemma
  (typ_equiv
    (t_array3 a)
    (t_array3 (close_array_group a))
  )
= ()

// Recursive type (needed by COSE Section 5.1 "Recipient")

// Inspiring from Barthe et al., Type-Based Termination with Sized
// Products (CSL 2008): we allow recursion only at the level of
// destructors. In other words, instead of having a generic recursion
// combinator, we provide a recursion-enabled version only for each
// destructor combinator. We need to annotate it with a bound b (akin
// to the "size" annotation in a sized type.)

let rec t_array3_rec
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> array_group3 (Some b)))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
=
  Cbor.Array? x &&
  match_array_group3 (phi x (t_array3_rec phi)) (Cbor.Array?.v x)


let array_group_parser_spec_arg
  (source: array_group3 None)
: Tot Type0
= (x: list Cbor.raw_data_item {
   match source x with
   | Some (_, []) -> True
   | _ -> False
  })

let array_group_parser_spec_ret
  (source: array_group3 None)
  (#target: Type0)
  (target_size: target -> GTot nat)
  (target_prop: target -> prop)
  (x: array_group_parser_spec_arg source)
: Tot Type0
= (y: target { 
    target_size y == List.Tot.length x /\
    target_prop y
  })

let array_group_parser_spec
  (source: array_group3 None)
  (#target: Type0)
  (target_size: target -> GTot nat)
  (target_prop: target -> prop)
: Type0
= (x: array_group_parser_spec_arg source) -> GTot (array_group_parser_spec_ret source target_size target_prop x)

let array_group_serializer_spec
  (#source: array_group3 None)
  (#target: Type0)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: array_group_parser_spec source target_size target_prop)
: Type0
= (x: target { target_prop x }) -> GTot (y: array_group_parser_spec_arg source {
    p y == x
  })

[@@erasable]
noeq
type ag_spec
  (source: array_group3 None)
  (target: Type0)
= {
  ag_size: target -> GTot nat;
  ag_serializable: target -> prop;
  ag_parser: array_group_parser_spec source ag_size ag_serializable;
  ag_serializer: array_group_serializer_spec ag_parser;
}

let ag_spec_coerce_target_prop
  (#source: array_group3 None)
  (#target: Type0)
  (p: ag_spec source target)
  (target_size': target -> GTot nat {
    forall x . target_size' x == p.ag_size x
  })
  (target_prop': target -> prop {
    forall x . target_prop' x <==> p.ag_serializable x
  })
: ag_spec source target
= {
  ag_size = target_size';
  ag_serializable = target_prop';
  ag_parser = (p.ag_parser <: array_group_parser_spec source target_size' target_prop');
  ag_serializer = p.ag_serializer;
}

let parser_spec_array_group
  (#source: array_group3 None)
  (#target: Type0)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: array_group_parser_spec source target_size target_prop)
  (target_prop' : target -> prop {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64) // serializability condition
  })
: Tot (parser_spec (t_array3 source) target target_prop')
= fun x -> let Cbor.Array a = x in p a

let serializer_spec_array_group
  (#source: array_group3 None)
  (#target: Type0)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p)
  (target_prop' : target -> prop {
    forall x . target_prop' x <==> (target_prop x /\ target_size x < pow2 64) // serializability condition
  })
: Tot (serializer_spec (parser_spec_array_group p target_prop'))
= fun x -> Cbor.Array (s x)

let spec_array_group_serializable
  (#source: array_group3 None)
  (#target: Type0)
  (p: ag_spec source target)
  (x: target)
: Tot prop
= p.ag_serializable x /\
  p.ag_size x < pow2 64

let spec_array_group
  (#source: array_group3 None)
  (#target: Type0)
  (p: ag_spec source target)
: Tot (spec (t_array3 source) target)
= {
  serializable = spec_array_group_serializable p;
  parser = parser_spec_array_group p.ag_parser _;
  serializer = serializer_spec_array_group p.ag_serializer _;
}

let array_group_parser_spec_bij
  (#source: array_group3 None)
  (#target1: Type0)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (f: array_group_parser_spec source target_size1 target_prop1)
  (#target2: Type0)
  (target_size2: target2 -> GTot nat)
  (target_prop2: target2 -> prop)
  (bij: bijection target1 target2 {
    (forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)) /\
    (forall x2 . target_prop2 x2 <==> target_prop1 (bij.bij_to_from x2))
  })
: Tot (array_group_parser_spec source target_size2 target_prop2)
= fun x -> bij.bij_from_to (f x)

let array_group_serializer_spec_bij
  (#source: array_group3 None)
  (#target1: Type0)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (#f: array_group_parser_spec source target_size1 target_prop1)
  (s: array_group_serializer_spec f)
  (#target2: Type0)
  (target_size2: target2 -> GTot nat)
  (target_prop2: target2 -> prop)
  (bij: bijection target1 target2 {
    (forall x2 . target_size2 x2 == target_size1 (bij.bij_to_from x2)) /\
    (forall x2 . target_prop2 x2 <==> target_prop1 (bij.bij_to_from x2))
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_bij f target_size2 target_prop2 bij))
= fun x -> s (bij.bij_to_from x)

let ag_spec_bij_size
  (#source: array_group3 None)
  (#target1: Type0)
  (f: ag_spec source target1)
  (#target2: Type0)
  (bij: bijection target1 target2)
  (x2: target2)
: GTot nat
= f.ag_size (bij.bij_to_from x2)

let ag_spec_bij_serializable
  (#source: array_group3 None)
  (#target1: Type0)
  (f: ag_spec source target1)
  (#target2: Type0)
  (bij: bijection target1 target2)
  (x2: target2)
: Tot prop
= f.ag_serializable (bij.bij_to_from x2)

let ag_spec_bij
  (#source: array_group3 None)
  (#target1: Type0)
  (f: ag_spec source target1)
  (#target2: Type0)
  (bij: bijection target1 target2)
: Tot (ag_spec source target2)
= {
  ag_size = ag_spec_bij_size f bij;
  ag_serializable = ag_spec_bij_serializable f bij;
  ag_parser = array_group_parser_spec_bij f.ag_parser _ _ bij;
  ag_serializer = array_group_serializer_spec_bij f.ag_serializer _ _ bij;
}

let array_group_parser_spec_item
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> GTot prop)
  (p: parser_spec ty target target_prop)
  (target_size: target -> GTot nat {
    forall x . target_size x == 1
  })
: Tot (array_group_parser_spec (array_group3_item ty) target_size target_prop)
= fun x -> let [hd] = x in p hd

let array_group_serializer_spec_item
  (#ty: typ)
  (#target: Type)
  (#target_prop: target -> GTot prop)
  (#p: parser_spec ty target target_prop)
  (s: serializer_spec p)
  (target_size: target -> GTot nat {
    forall x . target_size x == 1
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_item p target_size))
= fun x -> [s x]

let ag_spec_item_size
  (target: Type)
  (x: target)
: GTot nat
= 1

let ag_spec_item
  (#ty: typ)
  (#target: Type)
  (p: spec ty target)
: Tot (ag_spec (array_group3_item ty) target)
= {
  ag_size = ag_spec_item_size target;
  ag_serializable = p.serializable;
  ag_parser = array_group_parser_spec_item p.parser _;
  ag_serializer = array_group_serializer_spec_item p.serializer _;
}

val array_group_parser_spec_concat
  (#source1: array_group3 None)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (p1: array_group_parser_spec source1 target_size1 target_prop1)
  (#source2: array_group3 None)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (p2: array_group_parser_spec source2 target_size2 target_prop2 {
    array_group3_concat_unique_weak source1 source2
  })
  (target_size: (target1 & target2) -> GTot nat {
    forall x . target_size x == target_size1 (fst x) + target_size2 (snd x)
  })
  (target_prop: (target1 & target2) -> prop {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
: Tot (array_group_parser_spec (array_group3_concat source1 source2) target_size target_prop)

val array_group_parser_spec_concat_eq
  (#source1: array_group3 None)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (p1: array_group_parser_spec source1 target_size1 target_prop1)
  (#source2: array_group3 None)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (p2: array_group_parser_spec source2 target_size2 target_prop2 {
    array_group3_concat_unique_weak source1 source2
  })
  (target_size: (target1 & target2) -> GTot nat {
    forall x . target_size x == target_size1 (fst x) + target_size2 (snd x)
  })
  (target_prop: (target1 & target2) -> prop {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
  (x: array_group_parser_spec_arg (array_group3_concat source1 source2))
: Lemma
  (array_group_parser_spec_concat p1 p2 target_size target_prop x == (
    let Some (x1, x2) = source1 x in
    (p1 x1, p2 x2)
  ))
  [SMTPat (array_group_parser_spec_concat p1 p2 target_size target_prop x)]

let array_group_serializer_spec_concat
  (#source1: array_group3 None)
  (#target1: Type)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (#p1: array_group_parser_spec source1 target_size1 target_prop1)
  (s1: array_group_serializer_spec p1)
  (#source2: array_group3 None)
  (#target2: Type)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (#p2: array_group_parser_spec source2 target_size2 target_prop2)
  (s2: array_group_serializer_spec p2 {
    array_group3_concat_unique_weak source1 source2
  })
  (target_size: (target1 & target2) -> GTot nat {
    forall x . target_size x == target_size1 (fst x) + target_size2 (snd x)
  })
  (target_prop: (target1 & target2) -> prop {
    forall x . target_prop x <==> (target_prop1 (fst x) /\ target_prop2 (snd x))
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_concat p1 p2 target_size target_prop))
= fun x ->
    let (x1, x2) = x in
    let l1 = s1 x1 in
    let l2 = s2 x2 in
    let res = l1 `List.Tot.append` l2 in
    array_group3_concat_unique_weak_elim2 source1 source2 l1 l2;
    res

let ag_spec_concat_size
  (#source1: array_group3 None)
  (#target1: Type)
  (p1: ag_spec source1 target1)
  (#source2: array_group3 None)
  (#target2: Type)
  (p2: ag_spec source2 target2)
  (x: (target1 & target2))
: GTot nat
= p1.ag_size (fst x) + p2.ag_size (snd x)

let ag_spec_concat_serializable
  (#source1: array_group3 None)
  (#target1: Type)
  (p1: ag_spec source1 target1)
  (#source2: array_group3 None)
  (#target2: Type)
  (p2: ag_spec source2 target2)
  (x: (target1 & target2))
: Tot prop
= p1.ag_serializable (fst x) /\ p2.ag_serializable (snd x)

let ag_spec_concat
  (#source1: array_group3 None)
  (#target1: Type)
  (p1: ag_spec source1 target1)
  (#source2: array_group3 None)
  (#target2: Type)
  (p2: ag_spec source2 target2 {
    array_group3_concat_unique_weak source1 source2
  })
: Tot (ag_spec (array_group3_concat source1 source2) (target1 & target2))
= {
  ag_size = ag_spec_concat_size p1 p2;
  ag_serializable = ag_spec_concat_serializable p1 p2;
  ag_parser = array_group_parser_spec_concat p1.ag_parser p2.ag_parser _ _;
  ag_serializer = array_group_serializer_spec_concat p1.ag_serializer p2.ag_serializer _ _;
}

let rec array_group_parser_spec_zero_or_more'
  (#source: array_group3 None)
  (#target: Type)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: array_group_parser_spec source target_size target_prop {
    array_group3_concat_unique_strong source source
  })
  (target_size' : list target -> GTot nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (target_prop' : list target -> prop {
    forall x . target_prop' x <==> (forall y . List.Tot.memP y x ==> target_prop y)
  })
  (x: array_group_parser_spec_arg (array_group3_zero_or_more source))
: GTot (array_group_parser_spec_ret (array_group3_zero_or_more source) target_size' target_prop' x)
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
      array_group3_concat_unique_weak_zero_or_more_right source source;
      List.Tot.append_length l1 l2;
      let q = array_group_parser_spec_zero_or_more' p target_size' target_prop' l2 in
      p l1 :: q
    end

let array_group_parser_spec_zero_or_more
  (#source: array_group3 None)
  (#target: Type)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: array_group_parser_spec source target_size target_prop {
    array_group3_concat_unique_strong source source
  })
  (target_size' : list target -> GTot nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (target_prop' : list target -> prop {
    forall x . target_prop' x <==> (forall y . List.Tot.memP y x ==> target_prop y)
  })
: Tot (array_group_parser_spec (array_group3_zero_or_more source) target_size' target_prop')
= array_group_parser_spec_zero_or_more' p target_size' target_prop'

let array_group3_is_nonempty (a: array_group3 None) : Tot prop =
    forall l . match a l with
    | Some (consumed, _) -> Cons? consumed
    | _ -> True

let nonempty_array_group3 : Type0 =
  (a: array_group3 None { array_group3_is_nonempty a })

let rec array_group_serializer_spec_zero_or_more'
  (#source: nonempty_array_group3)
  (#target: Type)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p {
    array_group3_concat_unique_strong source source
  })
  (target_size' : list target -> GTot nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (target_prop' : list target -> prop {
    forall x . target_prop' x <==> (forall y . List.Tot.memP y x ==> target_prop y)
  })
  (x: list target { target_prop' x })
: GTot (y: array_group_parser_spec_arg (array_group3_zero_or_more source) {
    array_group_parser_spec_zero_or_more p target_size' target_prop' y == x
  })
  (decreases x)
= match x with
  | [] -> []
  | a :: q ->
    array_group3_concat_unique_weak_zero_or_more_right source source;
    let l1 = s a in
    let l2 = array_group_serializer_spec_zero_or_more' s target_size' target_prop' q in
    let res = l1 `List.Tot.append` l2 in
    res

let array_group_serializer_spec_zero_or_more
  (#source: nonempty_array_group3)
  (#target: Type)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p {
    array_group3_concat_unique_strong source source
  })
  (target_size' : list target -> GTot nat {
    forall (l: list target) . target_size' l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size' (List.Tot.tl l))
  })
  (target_prop' : list target -> prop {
    forall x . target_prop' x <==> (forall y . List.Tot.memP y x ==> target_prop y)
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_zero_or_more p target_size' target_prop'))
= array_group_serializer_spec_zero_or_more' s target_size' target_prop'

let rec ag_spec_zero_or_more_size
  (#source: array_group3 None)
  (#target: Type)
  (p: ag_spec source target)
  (l: list target)
: GTot nat
  (decreases l)
= match l with
  | [] -> 0
  | hd :: tl -> p.ag_size hd + ag_spec_zero_or_more_size p tl

let ag_spec_zero_or_more_serializable
  (#source: array_group3 None)
  (#target: Type)
  (p: ag_spec source target)
  (x: list target)
: Tot prop
= forall y . List.Tot.memP y x ==> p.ag_serializable y

let ag_spec_zero_or_more
  (#source: nonempty_array_group3)
  (#target: Type)
  (p: ag_spec source target {
    array_group3_concat_unique_strong source source
  })
: Tot (ag_spec (array_group3_zero_or_more source) (list target))
= {
  ag_size = ag_spec_zero_or_more_size p;
  ag_serializable = ag_spec_zero_or_more_serializable p;
  ag_parser = array_group_parser_spec_zero_or_more p.ag_parser _ _;
  ag_serializer = array_group_serializer_spec_zero_or_more p.ag_serializer _ _;
}

let array_group_parser_spec_one_or_more
  (#source: array_group3 None)
  (#target: Type)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: array_group_parser_spec source target_size target_prop {
    array_group3_concat_unique_strong source source
  })
  (target_size1 : list target -> GTot nat {
    forall (l: list target) . target_size1 l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size1 (List.Tot.tl l))
  })
  (target_prop1 : list target -> prop {
    forall x . target_prop1 x <==> (Cons? x /\ (forall y . List.Tot.memP y x ==> target_prop y))
  })
: Tot (array_group_parser_spec (array_group3_one_or_more source) target_size1 target_prop1)
= fun x ->
  array_group3_concat_unique_weak_zero_or_more_right source source;
  let Some (l1, l2) = source x in
  List.Tot.append_length l1 l2;
  p l1 :: array_group_parser_spec_zero_or_more p target_size1 (fun x -> Nil? x \/ target_prop1 x) l2

let array_group_serializer_spec_one_or_more
  (#source: nonempty_array_group3)
  (#target: Type)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p {
    array_group3_concat_unique_strong source source
  })
  (target_size1 : list target -> GTot nat {
    forall (l: list target) . target_size1 l == (if Nil? l then 0 else target_size (List.Tot.hd l) + target_size1 (List.Tot.tl l))
  })
  (target_prop1 : list target -> prop {
    forall x . target_prop1 x <==> (Cons? x /\ (forall y . List.Tot.memP y x ==> target_prop y))
  })
: Tot (array_group_serializer_spec (array_group_parser_spec_one_or_more p target_size1 target_prop1))
= fun x ->
  array_group3_concat_unique_weak_zero_or_more_right source source;
  let hd :: tl = x in
  let l1 = s hd in
  let l2 = array_group_serializer_spec_zero_or_more s target_size1 (fun x -> Nil? x \/ target_prop1 x) tl in
  List.Tot.append_length l1 l2;
  l1 `List.Tot.append` l2

let ag_spec_one_or_more_serializable
  (#source: array_group3 None)
  (#target: Type)
  (p: ag_spec source target)
  (x: list target)
: Tot prop
= Cons? x /\
  ag_spec_zero_or_more_serializable p x

let ag_spec_one_or_more
  (#source: nonempty_array_group3)
  (#target: Type)
  (p: ag_spec source target {
    array_group3_concat_unique_strong source source
  })
: Tot (ag_spec (array_group3_one_or_more source) (list target))
= {
  ag_size = ag_spec_zero_or_more_size p;
  ag_serializable = ag_spec_one_or_more_serializable p;
  ag_parser = array_group_parser_spec_one_or_more p.ag_parser _ _;
  ag_serializer = array_group_serializer_spec_one_or_more p.ag_serializer _ _;
}

let array_group_parser_spec_choice
  (#source1: array_group3 None)
  (#target1: Type0)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (p1: array_group_parser_spec source1 target_size1 target_prop1)
  (#source2: array_group3 None)
  (#target2: Type0)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (p2: array_group_parser_spec source2 target_size2 target_prop2)
  (target_size: (target1 `either` target2) -> GTot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> prop {
    forall x . target_prop x <==> begin match x with
    | Inl x1 -> target_prop1 x1
    | Inr x2 -> target_prop2 x2
    end
  })
: Tot (array_group_parser_spec (source1 `array_group3_choice` source2) target_size target_prop)
= fun x ->
    if Some? (source1 x)
    then Inl (p1 x)
    else Inr (p2 x)

let array_group_serializer_spec_choice
  (#source1: array_group3 None)
  (#target1: Type0)
  (#target_size1: target1 -> GTot nat)
  (#target_prop1: target1 -> prop)
  (#p1: array_group_parser_spec source1 target_size1 target_prop1)
  (s1: array_group_serializer_spec p1)
  (#source2: array_group3 None)
  (#target2: Type0)
  (#target_size2: target2 -> GTot nat)
  (#target_prop2: target2 -> prop)
  (#p2: array_group_parser_spec source2 target_size2 target_prop2)
  (s2: array_group_serializer_spec p2 { source1 `array_group3_disjoint` source2 }) // disjointness needed to avoid the CBOR object serialized from one case to be parsed into the other case
  (target_size: (target1 `either` target2) -> GTot nat {
    forall x . target_size x == begin match x with
    | Inl y -> target_size1 y
    | Inr y -> target_size2 y
    end
  })
  (target_prop: (target1 `either` target2) -> prop {
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
  (#source1: array_group3 None)
  (#target1: Type0)
  (p1: ag_spec source1 target1)
  (#source2: array_group3 None)
  (#target2: Type0)
  (p2: ag_spec source2 target2)
  (x: either target1 target2)
: GTot nat
= match x with
  | Inl x1 -> p1.ag_size x1
  | Inr x2 -> p2.ag_size x2

let ag_spec_choice_serializable
  (#source1: array_group3 None)
  (#target1: Type0)
  (p1: ag_spec source1 target1)
  (#source2: array_group3 None)
  (#target2: Type0)
  (p2: ag_spec source2 target2)
  (x: either target1 target2)
: GTot prop
= match x with
  | Inl x1 -> p1.ag_serializable x1
  | Inr x2 -> p2.ag_serializable x2

let ag_spec_choice
  (#source1: array_group3 None)
  (#target1: Type0)
  (p1: ag_spec source1 target1)
  (#source2: array_group3 None)
  (#target2: Type0)
  (p2: ag_spec source2 target2  { source1 `array_group3_disjoint` source2 })
: Tot (ag_spec (source1 `array_group3_choice` source2) (either target1 target2))
= {
  ag_size = ag_spec_choice_size p1 p2;
  ag_serializable = ag_spec_choice_serializable p1 p2;
  ag_parser = array_group_parser_spec_choice p1.ag_parser p2.ag_parser _ _;
  ag_serializer = array_group_serializer_spec_choice p1.ag_serializer p2.ag_serializer _ _;
}

let array_group_parser_spec_zero_or_one
  (#source: array_group3 None)
  (#target: Type)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (p: array_group_parser_spec source target_size target_prop)
  (target_size': option target -> GTot nat {
    forall x . target_size' x == begin match x with
    | None -> 0
    | Some x -> target_size x
    end
  })
  (target_prop': option target -> prop {
    forall x . target_prop' x <==> begin match x with
    | None -> True
    | Some x -> target_prop x
    end
  })
: Tot (array_group_parser_spec (array_group3_zero_or_one source) target_size' target_prop')
= fun x ->
    if Some? (source x)
    then Some (p x)
    else None

let array_group_serializer_spec_zero_or_one
  (#source: nonempty_array_group3) // needed because the empty case must map to None only
  (#target: Type)
  (#target_size: target -> GTot nat)
  (#target_prop: target -> prop)
  (#p: array_group_parser_spec source target_size target_prop)
  (s: array_group_serializer_spec p)
  (target_size': option target -> GTot nat {
    forall x . target_size' x == begin match x with
    | None -> 0
    | Some x -> target_size x
    end
  })
  (target_prop': option target -> prop {
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
  (#source: nonempty_array_group3)
  (#target: Type)
  (p: ag_spec source target)
  (x: option target)
: GTot nat
= match x with
  | None -> 0
  | Some x' -> p.ag_size x'

let ag_spec_zero_or_one_serializable
  (#source: nonempty_array_group3)
  (#target: Type)
  (p: ag_spec source target)
  (x: option target)
: Tot prop
= match x with
  | None -> True
  | Some x' -> p.ag_serializable x'

let ag_spec_zero_or_one
  (#source: nonempty_array_group3)
  (#target: Type)
  (p: ag_spec source target)
: Tot (ag_spec (array_group3_zero_or_one source) (option target))
= {
  ag_size = ag_spec_zero_or_one_size p;
  ag_serializable = ag_spec_zero_or_one_serializable p;
  ag_parser = array_group_parser_spec_zero_or_one p.ag_parser _ _;
  ag_serializer = array_group_serializer_spec_zero_or_one p.ag_serializer _ _;
}
