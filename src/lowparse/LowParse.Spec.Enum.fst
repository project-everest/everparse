module LowParse.Spec.Enum
include LowParse.Spec.Combinators

module L = FStar.List.Tot

[@Norm]
let rec list_map
  (#a #b: Type)
  (f: (a -> Tot b))
  (l: list a)
: Tot (l' : list b { l' == L.map f l } )
= match l with
  | [] -> []
  | a :: q -> f a :: list_map f q

type enum (key: eqtype) (repr: eqtype) = (l: list (key * repr) {
  L.noRepeats (list_map fst l) /\
  L.noRepeats (list_map snd l)
})

[@Norm]
let rec list_mem
  (#t: eqtype)
  (x: t)
  (l: list t)
: Tot (y: bool { y == true <==> L.mem x l == true } )
= match l with
  | [] -> false
  | a :: q -> (x = a || list_mem x q)

inline_for_extraction
let enum_key (#key #repr: eqtype) (e: enum key repr) : Tot eqtype = (s: key { list_mem s (list_map fst e) } )

inline_for_extraction
let make_enum_key (#key #repr: eqtype) (e: enum key repr) (k: key) : Pure (enum_key e)
  (requires (list_mem k (list_map fst e)))
  (ensures (fun k' -> k == (k' <: key)))
= k

inline_for_extraction
let enum_repr (#key #repr: eqtype) (e: enum key repr) : Tot eqtype = (r: repr { list_mem r (list_map snd e) } )

let flip (#a #b: Type) (c: (a * b)) : Tot (b * a) = let (ca, cb) = c in (cb, ca)

let rec map_flip_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map flip (list_map flip l) == l)
= match l with
  | [] -> ()
  | _ :: q -> map_flip_flip q

let rec map_fst_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map fst (list_map flip l) == list_map snd l)
= match l with
  | [] -> ()
  | _ :: q -> map_fst_flip q

let rec map_snd_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map snd (list_map flip l) == list_map fst l)
= match l with
  | [] -> ()
  | _ :: q -> map_snd_flip q

let rec assoc_mem_snd
  (#a #b: eqtype)
  (l: list (a * b))
  (x: a)
  (y: b)
: Lemma
  (requires (L.assoc x l == Some y))
  (ensures (list_mem y (list_map snd l) == true))
  (decreases l)
= let ((x', y') :: l') = l in
  if x' = x
  then ()
  else assoc_mem_snd l' x y

let rec assoc_flip_elim
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    L.noRepeats (list_map fst l) /\
    L.noRepeats (list_map snd l) /\
    L.assoc y (list_map flip l) == Some x
  ))
  (ensures (
    L.assoc x l == Some y
  ))
  (decreases l)
= let ((x', y') :: l') = l in
  if y' = y
  then ()
  else begin
    if x' = x
    then begin
      assert (list_mem x' (list_map fst l') == false);
      assoc_mem_snd (list_map flip l') y x;
      map_snd_flip l';
      assert False
    end
    else
      assoc_flip_elim l' y x
  end

let rec assoc_flip_intro
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    L.noRepeats (list_map fst l) /\
    L.noRepeats (list_map snd l) /\
    L.assoc x l == Some y
  ))
  (ensures (
    L.assoc y (list_map flip l) == Some x
  ))
= map_fst_flip l;
  map_snd_flip l;
  map_flip_flip l;
  assoc_flip_elim (list_map flip l) x y

let enum_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: enum_repr e)
: Pure (enum_key e)
  (requires True)
  (ensures (fun y -> L.assoc y e == Some r))
= map_fst_flip e;
  let e' = list_map #(key * repr) #(repr * key) flip e in
  L.assoc_mem r e';
  let k = Some?.v (L.assoc r e') in
  assoc_flip_elim e r k;
  L.assoc_mem k e;
  (k <: enum_key e)

let parse_enum_key_cond
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: repr)
: GTot bool
= list_mem r (list_map snd e)

let parse_enum_key_synth
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: repr { parse_enum_key_cond e r == true } )
: GTot (enum_key e)
= enum_key_of_repr e r

let parse_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
: Tot (parser (parse_filter_kind k) (enum_key e))
= (p
    `parse_filter`
    parse_enum_key_cond e
  )
  `parse_synth`
  parse_enum_key_synth e

let enum_repr_of_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Pure (enum_repr e)
  (requires True)
  (ensures (fun r -> L.assoc k e == Some r))
= L.assoc_mem k e;
  let r = Some?.v (L.assoc k e) in
  assoc_flip_intro e r k;
  L.assoc_mem r (list_map flip e);
  map_fst_flip e;
  (r <: enum_repr e)

let enum_repr_of_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: enum_repr e)
: Lemma
  (enum_repr_of_key e (enum_key_of_repr e r) == r)
= ()

let enum_key_of_repr_of_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Lemma
  (enum_key_of_repr e (enum_repr_of_key e k) == k)
= assoc_flip_intro e (enum_repr_of_key e k) k

let serialize_enum_key_synth_recip 
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: GTot (r: repr { parse_enum_key_cond e r == true } )
= enum_repr_of_key e k

let serialize_enum_key_synth_inverse
  (#key #repr: eqtype)
  (e: enum key repr)
: Lemma
  (synth_inverse (parse_enum_key_synth e) (serialize_enum_key_synth_recip e))
= Classical.forall_intro (enum_key_of_repr_of_key e)

let serialize_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Tot (serializer (parse_enum_key p e))
= serialize_enum_key_synth_inverse e;
  serialize_synth
    (parse_filter p (parse_enum_key_cond e))
    (parse_enum_key_synth e)
    (serialize_filter s (parse_enum_key_cond e))
    (serialize_enum_key_synth_recip e)
    ()

let serialize_enum_key_eq
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
  (x: enum_key e)
: Lemma
  (serialize (serialize_enum_key p s e) x == serialize s (enum_repr_of_key e x))
= serialize_enum_key_synth_inverse e;
  serialize_synth_eq
    (parse_filter p (parse_enum_key_cond e))
    (parse_enum_key_synth e)
    (serialize_filter s (parse_enum_key_cond e))
    (serialize_enum_key_synth_recip e)
    ()
    x

inline_for_extraction
let unknown_enum_repr (#key #repr: eqtype) (e: enum key repr) : Tot Type =
  (r: repr { list_mem r (list_map snd e) == false } )

type maybe_enum_key (#key #repr: eqtype) (e: enum key repr) =
| Known of (enum_key e)
| Unknown of (unknown_enum_repr e)

let maybe_enum_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: repr)
: Tot (maybe_enum_key e)
= if list_mem r (list_map snd e)
  then Known (enum_key_of_repr e r)
  else Unknown r

let parse_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
: Tot (parser k (maybe_enum_key e))
= p `parse_synth` (maybe_enum_key_of_repr e)

let parse_maybe_enum_key_eq
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
  (input: bytes)
: Lemma
  (parse (parse_maybe_enum_key p e) input == (match parse p input with
  | Some (x, consumed) -> Some (maybe_enum_key_of_repr e x, consumed)
  | _ -> None
  ))
= parse_synth_eq p (maybe_enum_key_of_repr e) input

let parse_enum_key_eq
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
  (input: bytes)
: Lemma
  (parse (parse_enum_key p e) input == (match parse p input with
  | Some (x, consumed) ->
    begin match maybe_enum_key_of_repr e x with
    | Known k -> Some (k, consumed)
    | _ -> None
    end
  | _ -> None
  ))
= parse_filter_eq p (parse_enum_key_cond e) input;
  parse_synth_eq (p `parse_filter` parse_enum_key_cond e) (parse_enum_key_synth e) input

let repr_of_maybe_enum_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (x: maybe_enum_key e)
: Tot (r: repr { maybe_enum_key_of_repr e r == x } )
= match x with
  | Known k' ->
    enum_key_of_repr_of_key e k' ;
    enum_repr_of_key e k'
  | Unknown r -> r

let serialize_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Tot (serializer (parse_maybe_enum_key p e))
= serialize_synth p (maybe_enum_key_of_repr e) s (repr_of_maybe_enum_key e) ()

let serialize_maybe_enum_key_eq
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
  (x: maybe_enum_key e)
: Lemma
  (serialize (serialize_maybe_enum_key p s e) x == serialize s (repr_of_maybe_enum_key e x))
= serialize_synth_eq p (maybe_enum_key_of_repr e) s (repr_of_maybe_enum_key e) () x 

let is_total_enum (#key: eqtype) (#repr: eqtype) (l: list (key * repr)) : GTot Type0 =
  forall (k: key) . {:pattern (list_mem k (list_map fst l))} list_mem k (list_map fst l)

let total_enum (key: eqtype) (repr: eqtype) : Tot eqtype =
  (l: enum key repr { is_total_enum l } )

let synth_total_enum_key
  (#key: eqtype)
  (#repr: eqtype)
  (l: total_enum key repr)
  (k: enum_key l)
: Tot key
= let k' : key = k in
  k'

let parse_total_enum_key
  (#k: parser_kind)
  (#key: eqtype)
  (#repr: eqtype)
  (p: parser k repr)
  (l: total_enum key repr)
: Tot (parser (parse_filter_kind k) key)
= parse_enum_key p l `parse_synth` (synth_total_enum_key l)

let synth_total_enum_key_recip
  (#key: eqtype)
  (#repr: eqtype)
  (l: total_enum key repr)
  (k: key)
: Tot (k' : enum_key l { synth_total_enum_key l k' == k } )
= k

let serialize_total_enum_key
  (#k: parser_kind)
  (#key: eqtype)
  (#repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (l: total_enum key repr)
: Tot (serializer (parse_total_enum_key p l))
= serialize_synth (parse_enum_key p l) (synth_total_enum_key l) (serialize_enum_key p s l) (synth_total_enum_key_recip l) ()

type maybe_total_enum_key (#key #repr: eqtype) (e: total_enum key repr) =
| TotalKnown of key
| TotalUnknown of (unknown_enum_repr e)

let maybe_total_enum_key_of_repr
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (r: repr)
: Tot (maybe_total_enum_key e)
= if list_mem r (list_map snd e)
  then TotalKnown (enum_key_of_repr e r)
  else TotalUnknown r

let parse_maybe_total_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: total_enum key repr)
: Tot (parser k (maybe_total_enum_key e))
= p `parse_synth` (maybe_total_enum_key_of_repr e)

let repr_of_maybe_total_enum_key
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (k: maybe_total_enum_key e)
: Tot (r: repr { maybe_total_enum_key_of_repr e r == k } )
= match k with
  | TotalKnown k' ->
    enum_key_of_repr_of_key e k' ;
    enum_repr_of_key e k'
  | TotalUnknown r -> r

let serialize_maybe_total_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: total_enum key repr)
: Tot (serializer (parse_maybe_total_enum_key p e))
= serialize_synth p (maybe_total_enum_key_of_repr e) s (repr_of_maybe_total_enum_key e) ()

inline_for_extraction
let maybe_enum_key_of_total
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (k: maybe_total_enum_key e)
: Tot (maybe_enum_key e)
= match k with
  | TotalKnown ek -> Known (ek <: key)
  | TotalUnknown r -> Unknown r

inline_for_extraction
let total_of_maybe_enum_key
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (k: maybe_enum_key e)
: Tot (maybe_total_enum_key e)
= match k with
  | Known ek -> TotalKnown (ek <: key)
  | Unknown r -> TotalUnknown r

let maybe_total_enum_key_of_repr_eq
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (r: repr)
: Lemma
  (maybe_total_enum_key_of_repr e r == total_of_maybe_enum_key e (maybe_enum_key_of_repr e r))
= ()

let parse_maybe_total_enum_key_eq
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: total_enum key repr)
  (input: bytes)
: Lemma
  (parse (parse_maybe_total_enum_key p e) input == (parse (parse_maybe_enum_key p e `parse_synth` total_of_maybe_enum_key e) input))
= parse_synth_eq p (maybe_total_enum_key_of_repr e) input;
  parse_synth_eq (parse_maybe_enum_key p e) (total_of_maybe_enum_key e) input;
  parse_synth_eq p (maybe_enum_key_of_repr e) input

(* Destructors *)


(* Universal destructor *)

let r_reflexive_prop
  (t: Type)
  (r: (t -> t -> GTot Type0))
: GTot Type0
= forall (x: t) . {:pattern (r x x)} r x x

inline_for_extraction
let r_reflexive_t
  (t: Type)
  (r: (t -> t -> GTot Type0))
: Tot Type
= (x: t) -> Lemma (r x x)

let r_reflexive_t_elim
  (t: Type)
  (r: (t -> t -> GTot Type0))
  (phi: r_reflexive_t t r)
: Lemma
  (r_reflexive_prop t r)
= Classical.forall_intro phi

let r_transitive_prop
  (t: Type)
  (r: (t -> t -> GTot Type0))
: GTot Type0
= forall (x y z: t) . {:pattern (r x y); (r y z)} (r x y /\ r y z) ==> r x z

inline_for_extraction
let r_transitive_t
  (t: Type)
  (r: (t -> t -> GTot Type0))
: Tot Type
= (x: t) -> (y: t) -> (z: t) -> Lemma ((r x y /\ r y z) ==> r x z)

let r_transitive_t_elim
  (t: Type)
  (r: (t -> t -> GTot Type0))
  (phi: r_transitive_t t r)
: Lemma
  (r_transitive_prop t r)
= Classical.forall_intro_3 phi

inline_for_extraction
let if_combinator
  (t: Type)
  (eq: (t -> t -> GTot Type0))
: Tot Type
= (cond: bool) ->
  (sv_true: (cond_true cond -> Tot t)) ->
  (sv_false: (cond_false cond -> Tot t)) ->
  Tot (y: t { eq y (if cond then sv_true () else sv_false ()) } )

inline_for_extraction
let default_if
  (t: Type)
: Tot (if_combinator t (eq2 #t))
= fun
  (cond: bool)
  (s_true: (cond_true cond -> Tot t))
  (s_false: (cond_false cond -> Tot t))
-> (if cond
  then s_true ()
  else s_false ()) <: (y: t { y == (if cond then s_true () else s_false ()) } )

let feq
  (u v: Type)
  (eq: (v -> v -> GTot Type0))
  (f1 f2: (u -> Tot v))
: GTot Type0
= (forall (x: u) . {:pattern (f1 x); (f2 x)} eq (f1 x) (f2 x))

(* #!$% patterns on forall, the following proofs should be trivial and now they aren't *)

let feq_elim
  (u v: Type)
  (eq: (v -> v -> GTot Type0))
  (f1 f2: (u -> Tot v))
  (x: u)
: Lemma
  (requires (feq u v eq f1 f2))
  (ensures (f1 x `eq` f2 x))
= ()

let feq_intro
  (u v: Type)
  (eq: (v -> v -> GTot Type0))
  (f1 f2: (u -> Tot v))
  (phi: (x: u) -> Lemma (f1 x `eq` f2 x))
: Lemma (feq _ _ eq f1 f2)
= Classical.forall_intro phi

let feq_trans
  (u v: Type)
  (eq: (v -> v -> GTot Type0))
: Pure (r_transitive_t _ (feq _ _ eq))
  (requires (r_transitive_prop _ eq))
  (ensures (fun _ -> True))
= let phi
    (f1 f2 f3: (u -> Tot v))
  : Lemma
    (requires (feq _ _ eq f1 f2 /\ feq _ _ eq f2 f3))
    (ensures (feq _ _ eq f1 f3))
  = feq_intro _ _ eq f1 f3 (fun x -> assert (f1 x `eq` f2 x /\ f2 x `eq` f3 x))
  in
  let phi2
    (f1 f2 f3: (u -> Tot v))
  : Lemma
    ((feq _ _ eq f1 f2 /\ feq _ _ eq f2 f3) ==> feq _ _ eq f1 f3)
  = Classical.move_requires (phi f1 f2) f3
  in
  phi2

inline_for_extraction
let fif
  (u v: Type)
  (eq: (v -> v -> GTot Type0))
  (ifc: if_combinator v eq)
: Tot (if_combinator (u -> Tot v) (feq u v eq))
= fun (cond: bool) (s_true: (cond_true cond -> u -> Tot v)) (s_false: (cond_false cond -> u -> Tot v)) (x: u) ->
    ifc
      cond
      (fun h -> s_true () x)
      (fun h -> s_false () x)

inline_for_extraction
let enum_destr_t
  (t: Type)
  (#key #repr: eqtype)  
  (e: enum key repr)
: Tot Type
= (eq: (t -> t -> GTot Type0)) ->
  (ift: if_combinator t eq) ->
  (eq_refl: r_reflexive_t _ eq) ->
  (eq_trans: r_transitive_t _ eq) ->
  (f: ((x: enum_key e) -> Tot t)) ->
  (x: enum_key e) ->
  Tot (y: t { eq y (f x) } )

inline_for_extraction
let enum_tail'
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum key repr)
  (requires True)
  (ensures (fun y -> Cons? e ==> (let (_ :: y') = e in y == y')))
= match e with _ :: y -> y | _ -> []

inline_for_extraction
let enum_tail
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (enum key repr)
= enum_tail' e

inline_for_extraction
let enum_destr_cons
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
  (g: enum_destr_t t (enum_tail' e))
: Pure (enum_destr_t t e)
  (requires (Cons? e))
  (ensures (fun _ -> True))
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  [@inline_let]
  let _ = r_transitive_t_elim _ _ eq_trans in
  (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, _) :: _ ->
     (fun (f: (enum_key e -> Tot t)) (x: enum_key e) -> ((
       [@inline_let]
       let f' : (enum_key (enum_tail' e) -> Tot t) =
         (fun (x' : enum_key (enum_tail' e)) ->
           [@inline_let]
           let (x_ : enum_key e) = (x' <: key) in
           f x_
         )
       in
       [@inline_let]
       let (y: t) =
       ift
         ((k <: key) = x)
         (fun h -> f k)
         (fun h ->
           [@inline_let]
           let x' : enum_key (enum_tail' e) = (x <: key) in
           (g eq ift eq_refl eq_trans f' x' <: t))
       in
       y
     ) <: (y: t { eq y (f x) } )))
  ) e

inline_for_extraction
let enum_destr_cons'
  (t: Type)
  (key repr: eqtype)
  (e: enum key repr)
  (u: unit { Cons? e } )
  (g: enum_destr_t t (enum_tail e))
: Tot (enum_destr_t t e)
= enum_destr_cons t e g

inline_for_extraction
let enum_destr_cons_nil
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum_destr_t t e)
  (requires (Cons? e /\ Nil? (enum_tail' e)))
  (ensures (fun _ -> True))
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, _) :: _ ->
     (fun (f: (enum_key e -> Tot t)) (x: enum_key e) -> ((
       f k
     ) <: (y: t { eq y (f x) } )))
  ) e

inline_for_extraction
let enum_destr_cons_nil'
  (t: Type)
  (key repr: eqtype)
  (e: enum key repr)
  (u1: unit { Cons? e } )
  (u2: unit { Nil? (enum_tail e) } )
: Tot (enum_destr_t t e)
= enum_destr_cons_nil t e

(* Dependent destructor *)

inline_for_extraction
let dep_enum_destr
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (enum_key e -> Tot (Type u#a)))
: Tot (Type)
= (v_eq: ((k: enum_key e) -> v k -> v k -> GTot Type0)) ->
  (v_if: ((k: enum_key e) -> Tot (if_combinator (v k) (v_eq k)))) ->
  (v_eq_refl: ((k: enum_key e) -> Tot (r_reflexive_t _ (v_eq k)))) ->
  (v_eq_trans: ((k: enum_key e) -> Tot (r_transitive_t _ (v_eq k)))) ->
  (f: ((k: enum_key e) -> Tot (v k))) ->
  (k: enum_key e) ->
  Tot (y: v k { v_eq k y (f k) } )

module L = FStar.List.Tot

inline_for_extraction
let dep_enum_destr_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (u: squash (Cons? e))
  (v: (enum_key e -> Tot Type))
  (destr: dep_enum_destr (enum_tail e) (fun (k' : enum_key (enum_tail e)) -> v (k' <: key)))
: Tot (dep_enum_destr e v)
= match e with
  | ((k, _) :: _) ->
    fun
    (v_eq: ((k: enum_key e) -> v k -> v k -> GTot Type0))
    (v_if: ((k: enum_key e) -> Tot (if_combinator (v k) (v_eq k))))
    (v_eq_refl: ((k: enum_key e) -> Tot (r_reflexive_t _ (v_eq k))))
    (v_eq_trans: ((k: enum_key e) -> Tot (r_transitive_t _ (v_eq k))))
    (f: ((k: enum_key e) -> Tot (v k)))
    (k' : enum_key e) ->
    [@inline_let]
    let _ = r_reflexive_t_elim (v k') (v_eq k') (v_eq_refl k') in
    [@inline_let]
    let _ = r_transitive_t_elim (v k') (v_eq k') (v_eq_trans k') in  
    [@inline_let]
    let y : v k' =
      v_if k' (k = k') (fun _ ->
        [@inline_let]
        let y : v k' = f k in
        y
      ) (fun _ ->
        [@inline_let]
        let v' (k: enum_key (enum_tail e)) : Tot Type = v (k <: key) in
        [@inline_let]
        let v'_eq (k: enum_key (enum_tail e)) : Tot (v' k -> v' k -> GTot Type0) = v_eq (k <: key) in
        [@inline_let]
        let v'_if (k: enum_key (enum_tail e)) : Tot (if_combinator (v' k) (v'_eq k)) = v_if (k <: key) in
        [@inline_let]
        let v'_eq_refl (k: enum_key (enum_tail e)) : Tot (r_reflexive_t _ (v'_eq k)) = v_eq_refl (k <: key) in
        [@inline_let]
        let v'_eq_trans (k: enum_key (enum_tail e)) : Tot (r_transitive_t _ (v'_eq k)) = v_eq_trans (k <: key) in
        [@inline_let]
        let f' (k: enum_key (enum_tail e)) : Tot (v' k) = f (k <: key) in
        [@inline_let]
        let k' : key = k' in
        [@inline_let]
        let _ = assert (k' <> k) in
        [@inline_let]
        let _ = assert (L.mem k' (L.map fst (enum_tail e))) in
        [@inline_let]
        let (y: v' k') =
          destr v'_eq v'_if v'_eq_refl v'_eq_trans f' k'
        in
        y
      )
    in
    (y <: (y: v k' { v_eq k' y (f k') } ))

inline_for_extraction
let dep_enum_destr_cons_nil
  (#key #repr: eqtype)
  (e: enum key repr)
  (u: squash (Cons? e /\ Nil? (enum_tail e)))
  (v: (enum_key e -> Tot Type))
: Tot (dep_enum_destr e v)
= match e with
  | ((k, _) :: _) ->
    fun
    (v_eq: ((k: enum_key e) -> v k -> v k -> GTot Type0))
    (v_if: ((k: enum_key e) -> Tot (if_combinator (v k) (v_eq k))))
    (v_eq_refl: ((k: enum_key e) -> Tot (r_reflexive_t _ (v_eq k))))
    (v_eq_trans: ((k: enum_key e) -> Tot (r_transitive_t _ (v_eq k))))
    (f: ((k: enum_key e) -> Tot (v k)))
    (k' : enum_key e) ->
    [@inline_let]
    let _ = r_reflexive_t_elim (v k') (v_eq k') (v_eq_refl k') in
    [@inline_let]
    let _ = r_transitive_t_elim (v k') (v_eq k') (v_eq_trans k') in  
    [@inline_let]
    let y : v k' = f k in
    (y <: (y: v k' { v_eq k' y (f k') } ))

(* Destructor from the representation *)


let maybe_enum_key_of_repr_not_in (#key #repr: eqtype) (e: enum key repr) (l: list (key * repr)) (x: repr) : GTot Type0 =
  (~ (L.mem x (L.map snd l)))

let list_rev_cons
  (#t: Type)
  (a: t)
  (q: list t)
: Lemma
  (L.rev (a :: q) == L.rev q `L.append` [a])
= L.rev_rev' (a :: q);
  L.rev_rev' q

let list_append_rev_cons (#t: Type) (l1: list t) (x: t) (l2: list t) : Lemma
  (L.append (L.rev l1) (x :: l2) == L.append (L.rev (x :: l1)) l2)
= list_rev_cons x l1;
  L.append_assoc (L.rev l1) [x] l2

let rec assoc_append_flip_l_intro
  (#key #repr: eqtype)
  (l1 l2: list (key * repr))
  (y: repr)
  (x: key)
: Lemma
  (requires (L.noRepeats (L.map snd (L.append l1 l2)) /\ L.assoc y (L.map flip l2) == Some x))
  (ensures (L.assoc y (L.map flip (l1 `L.append` l2)) == Some x))
= match l1 with
  | [] -> ()
  | (_, r') :: q ->
    L.assoc_mem y (L.map flip l2);
    map_fst_flip l2;
    L.map_append snd l1 l2;
    L.noRepeats_append_elim (L.map snd l1) (L.map snd l2);
    assoc_append_flip_l_intro q l2 y x

inline_for_extraction
let maybe_enum_destr_t'
  (t: Type)
  (#key #repr: eqtype)  
  (e: enum key repr)
  (l1 l2: list (key * repr))
  (u1: squash (e == L.append (L.rev l1) l2))
: Tot Type
= (eq: (t -> t -> GTot Type0)) ->
  (ift: if_combinator t eq) ->
  (eq_refl: r_reflexive_t _ eq) ->
  (eq_trans: r_transitive_t _ eq) ->
  (f: ((x: maybe_enum_key e) -> Tot t)) ->
  (x: repr { maybe_enum_key_of_repr_not_in e l1 x } ) ->
  Tot (y: t { eq y (f (maybe_enum_key_of_repr e x)) } )

inline_for_extraction
let maybe_enum_destr_t
  (t: Type)
  (#key #repr: eqtype)  
  (e: enum key repr)
: Tot Type
= (eq: (t -> t -> GTot Type0)) ->
  (ift: if_combinator t eq) ->
  (eq_refl: r_reflexive_t _ eq) ->
  (eq_trans: r_transitive_t _ eq) ->
  (f: ((x: maybe_enum_key e) -> Tot t)) ->
  (x: repr) ->
  Tot (y: t { eq y (f (maybe_enum_key_of_repr e x)) } )

inline_for_extraction
let destr_maybe_total_enum_repr
  (#t: Type)
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (destr: maybe_enum_destr_t t e)
  (eq: (t -> t -> GTot Type0))
  (ift: if_combinator t eq)
  (eq_refl: r_reflexive_t _ eq)
  (eq_trans: r_transitive_t _ eq)
  (f: ((x: maybe_total_enum_key e) -> Tot t))
  (x: repr)
: Tot (y: t { eq y (f (maybe_total_enum_key_of_repr e x)) } )
= destr eq ift eq_refl eq_trans (fun y -> f (total_of_maybe_enum_key e y)) x

inline_for_extraction
let maybe_enum_destr_t_intro
  (t: Type)
  (#key #repr: eqtype)  
  (e: enum key repr)
  (f: maybe_enum_destr_t' t e [] e ())
: Tot (maybe_enum_destr_t t e)
= f

let maybe_enum_key_of_repr_not_in_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: key)
  (r: repr)
  (l: list (key * repr))
  (x: repr)
: Lemma
  (requires (maybe_enum_key_of_repr_not_in e l x /\ x <> r))
  (ensures (maybe_enum_key_of_repr_not_in e ((k, r) :: l) x))
= ()

[@Norm]
inline_for_extraction
let list_hd
  (#t: Type)
  (l: list t { Cons? l } )
= match l with
  | a :: _ -> a

[@Norm]
inline_for_extraction
let list_tl
  (#t: Type)
  (l: list t { Cons? l } )
= match l with
  | _ :: q -> q


inline_for_extraction
let maybe_enum_destr_cons
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
  (l1: list (key * repr))
  (l2: list (key * repr))
  (u1: squash (Cons? l2 /\ e == L.append (L.rev l1) l2))
  (g: (maybe_enum_destr_t' t e (list_hd l2 :: l1) (list_tl l2) (list_append_rev_cons l1 (list_hd l2) (list_tl l2))))
: Tot (maybe_enum_destr_t' t e l1 l2 u1)
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) (f: (maybe_enum_key e -> Tot t)) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  [@inline_let]
  let _ = r_transitive_t_elim _ _ eq_trans in
  match list_hd l2 with
  | (k, r) ->
  [@inline_let]
  let _ : squash (L.mem k (L.map fst e)) =
    L.append_mem (L.map fst (L.rev l1)) (L.map fst l2) k;
    L.map_append fst (L.rev l1) (l2);
    ()
  in
  [@inline_let]
  let (_ : squash (maybe_enum_key_of_repr e r == Known k)) =
    L.append_mem (L.map snd (L.rev l1)) (L.map snd (l2)) r;
    L.map_append snd (L.rev l1) (l2);
    assoc_append_flip_l_intro (L.rev l1) (l2) r k;
    ()
  in
  fun (x: repr { maybe_enum_key_of_repr_not_in e l1 x } ) -> ((
    ift
      (x = r)
      (fun h -> f (Known k))
      (fun h -> g eq ift eq_refl eq_trans f x)
  ) <: (y: t { eq y (f (maybe_enum_key_of_repr e x)) } ))

let rec list_rev_map
  (#t1 #t2: Type)
  (f: t1 -> Tot t2)
  (l: list t1)
: Lemma
  (L.rev (L.map f l) == L.map f (L.rev l))
= match l with
  | [] -> ()
  | a :: q ->
    list_rev_cons a q;
    list_rev_cons (f a) (L.map f q);
    list_rev_map f q;
    L.map_append f (L.rev q) [a]

inline_for_extraction
let maybe_enum_destr_nil
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
  (l1: list (key * repr))
  (l2: list (key * repr))
  (u1: squash (Nil? l2 /\ e == L.append (L.rev l1) []))
: Tot (maybe_enum_destr_t' t e l1 l2 u1)
= fun (eq: (t -> t -> GTot Type0)) (ift: if_combinator t eq) (eq_refl: r_reflexive_t _ eq) (eq_trans: r_transitive_t _ eq) (f: (maybe_enum_key e -> Tot t)) ->
  [@inline_let]
  let _ = r_reflexive_t_elim _ _ eq_refl in
  [@inline_let]
  let _ = r_transitive_t_elim _ _ eq_trans in
  fun (x: repr { maybe_enum_key_of_repr_not_in e l1 x } ) -> ((
    L.append_l_nil (L.rev l1);
    list_rev_map snd l1;
    L.rev_mem (L.map snd l1) x;
    f (Unknown x)
  ) <: (y: t { eq y (f (maybe_enum_key_of_repr e x)) } ))

[@Norm]
let rec mk_maybe_enum_destr'
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
  (l1: list (key * repr))
  (l2: list (key * repr))
  (u: squash (e == L.rev l1 `L.append` l2))
: Tot (maybe_enum_destr_t' t e l1 l2 u)
  (decreases l2)
= match l2 with
  | [] -> maybe_enum_destr_nil t e l1 l2 u
  | _ ->
    [@inline_let]
    let _ = list_append_rev_cons l1 (list_hd l2) (list_tl l2) in
    maybe_enum_destr_cons t e l1 l2 u (mk_maybe_enum_destr' t e (list_hd l2 :: l1) (list_tl l2) u)

[@Norm]
let mk_maybe_enum_destr
  (t: Type)
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (maybe_enum_destr_t t e)
= maybe_enum_destr_t_intro t e (mk_maybe_enum_destr' t e [] e ())

(* dependent representation-based destructor *)

inline_for_extraction
let dep_maybe_enum_destr_t
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (maybe_enum_key e -> Tot Type))
: Tot Type
= (v_eq: ((k: maybe_enum_key e) -> v k -> v k -> GTot Type0)) ->
  (v_if: ((k: maybe_enum_key e) -> Tot (if_combinator (v k) (v_eq k)))) ->
  (v_eq_refl: ((k: maybe_enum_key e) -> Tot (r_reflexive_t _ (v_eq k)))) ->
  (v_eq_trans: ((k: maybe_enum_key e) -> Tot (r_transitive_t _ (v_eq k)))) ->
  (f: ((k: maybe_enum_key e) -> Tot (v k))) ->
  (r: repr) ->
  Tot (y: v (maybe_enum_key_of_repr e r) { v_eq (maybe_enum_key_of_repr e r) y (f (maybe_enum_key_of_repr e r)) } )

inline_for_extraction
let dep_maybe_enum_destr_t'
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (maybe_enum_key e -> Tot Type))
  (l1 l2: list (key * repr))
  (u1: squash (e == L.append (L.rev l1) l2))
: Tot Type
= (v_eq: ((k: maybe_enum_key e) -> v k -> v k -> GTot Type0)) ->
  (v_if: ((k: maybe_enum_key e) -> Tot (if_combinator (v k) (v_eq k)))) ->
  (v_eq_refl: ((k: maybe_enum_key e) -> Tot (r_reflexive_t _ (v_eq k)))) ->
  (v_eq_trans: ((k: maybe_enum_key e) -> Tot (r_transitive_t _ (v_eq k)))) ->
  (f: ((k: maybe_enum_key e) -> Tot (v k))) ->
  (r: repr { maybe_enum_key_of_repr_not_in e l1 r } ) ->
  Tot (y: v (maybe_enum_key_of_repr e r) { v_eq (maybe_enum_key_of_repr e r) y (f (maybe_enum_key_of_repr e r)) } )

inline_for_extraction
let dep_maybe_enum_destr_t_intro
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (maybe_enum_key e -> Tot Type))
  (d: dep_maybe_enum_destr_t' e v [] e ())
: Tot (dep_maybe_enum_destr_t e v)
= d

inline_for_extraction
let dep_maybe_enum_destr_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (maybe_enum_key e -> Tot Type))
  (l1: list (key * repr))
  (l2: list (key * repr))
  (u1: squash (Cons? l2 /\ e == L.append (L.rev l1) l2))
  (g: (dep_maybe_enum_destr_t' e v (list_hd l2 :: l1) (list_tl l2) (list_append_rev_cons l1 (list_hd l2) (list_tl l2))))
: Tot (dep_maybe_enum_destr_t' e v l1 l2 u1)
= fun
  (v_eq: ((k: maybe_enum_key e) -> v k -> v k -> GTot Type0))
  (v_if: ((k: maybe_enum_key e) -> Tot (if_combinator (v k) (v_eq k))))
  (v_eq_refl: ((k: maybe_enum_key e) -> Tot (r_reflexive_t _ (v_eq k))))
  (v_eq_trans: ((k: maybe_enum_key e) -> Tot (r_transitive_t _ (v_eq k))))
  (f: ((k: maybe_enum_key e) -> Tot (v k)))
  ->
  match list_hd l2 with
  | (k, r) ->
  [@inline_let]
  let _ : squash (L.mem k (L.map fst e)) =
    L.append_mem (L.map fst (L.rev l1)) (L.map fst l2) k;
    L.map_append fst (L.rev l1) (l2);
    ()
  in
  [@inline_let]
  let (_ : squash (maybe_enum_key_of_repr e r == Known k)) =
    L.append_mem (L.map snd (L.rev l1)) (L.map snd (l2)) r;
    L.map_append snd (L.rev l1) (l2);
    assoc_append_flip_l_intro (L.rev l1) (l2) r k;
    ()
  in
  fun (x: repr { maybe_enum_key_of_repr_not_in e l1 x } ) ->
    //NS: y is linear in the continuation after erasure; inline it
    [@inline_let]
    let y : v (maybe_enum_key_of_repr e x) =
      v_if
        (maybe_enum_key_of_repr e x) // TODO: Since we cannot make this argument ghost, we need to make the user aware of the fact that this argument must not be extracted.
        (x = r)
        (fun h -> f (Known k))
        (fun h ->
          g v_eq v_if v_eq_refl v_eq_trans f x)
    in
    [@inline_let]
    let _ : squash (v_eq (maybe_enum_key_of_repr e x) y (f (maybe_enum_key_of_repr e x))) =
      if x = r
      then ()
      else v_eq_trans (maybe_enum_key_of_repr e x) y (g v_eq v_if v_eq_refl v_eq_trans f x) (f (maybe_enum_key_of_repr e x))
    in
    (y <: (y: v (maybe_enum_key_of_repr e x) { v_eq (maybe_enum_key_of_repr e x) y (f (maybe_enum_key_of_repr e x)) } ))

inline_for_extraction
let dep_maybe_enum_destr_nil
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (maybe_enum_key e -> Tot Type))
  (l1: list (key * repr))
  (l2: list (key * repr))
  (u1: squash (Nil? l2 /\ e == L.append (L.rev l1) []))
: Tot (dep_maybe_enum_destr_t' e v l1 l2 u1)
= fun
  (v_eq: ((k: maybe_enum_key e) -> v k -> v k -> GTot Type0))
  (v_if: ((k: maybe_enum_key e) -> Tot (if_combinator (v k) (v_eq k))))
  (v_eq_refl: ((k: maybe_enum_key e) -> Tot (r_reflexive_t _ (v_eq k))))
  (v_eq_trans: ((k: maybe_enum_key e) -> Tot (r_transitive_t _ (v_eq k))))
  (f: ((k: maybe_enum_key e) -> Tot (v k)))
  (x: repr { maybe_enum_key_of_repr_not_in e l1 x } )
  -> ((
    L.append_l_nil (L.rev l1);
    list_rev_map snd l1;
    L.rev_mem (L.map snd l1) x;
    assert (Unknown x == maybe_enum_key_of_repr e x);
    //NS: y is linear in the continuation after erasure
    [@inline_let]
    let y : v (maybe_enum_key_of_repr e x) = f (Unknown x) in
    [@inline_let]
    let _ = v_eq_refl (maybe_enum_key_of_repr e x) (f (maybe_enum_key_of_repr e x)) in
    y
  ) <: (y: v (maybe_enum_key_of_repr e x) { v_eq (maybe_enum_key_of_repr e x) y (f (maybe_enum_key_of_repr e x)) } ))

[@Norm]
let rec mk_dep_maybe_enum_destr'
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (maybe_enum_key e -> Tot Type))
  (l1: list (key * repr))
  (l2: list (key * repr))
  (u1: squash (e == L.append (L.rev l1) l2))
: Tot (dep_maybe_enum_destr_t' e v l1 l2 u1)
  (decreases l2)
= match l2 with
  | [] -> dep_maybe_enum_destr_nil e v l1 l2 u1
  | _ -> dep_maybe_enum_destr_cons e v l1 l2 u1 (mk_dep_maybe_enum_destr' e v (list_hd l2 :: l1) (list_tl l2) (list_append_rev_cons l1 (list_hd l2) (list_tl l2)))

[@Norm]
let mk_dep_maybe_enum_destr
  (#key #repr: eqtype)
  (e: enum key repr)
  (v: (maybe_enum_key e -> Tot Type))
= dep_maybe_enum_destr_t_intro e v (mk_dep_maybe_enum_destr' e v [] e ())

(* Eliminators and destructors for verification purposes *)

let rec list_forallp (#t: Type) (p: t -> GTot Type0) (l: list t) : GTot Type0 =
  match l with
  | [] -> True
  | a :: q -> p a /\ list_forallp p q

let rec list_forallp_mem (#t: eqtype) (p: t -> GTot Type0) (l: list t) : Lemma
  (list_forallp p l <==> (forall x . L.mem x l ==> p x))
= match l with
  | [] -> ()
  | _ :: q -> list_forallp_mem p q

inline_for_extraction
let destruct_maybe_enum_key
  (#key #value: eqtype)
  (e: enum key value)
  (f: maybe_enum_key e -> Tot Type)
  (f_known: (
    (x: key) ->
    (u: squash (list_mem x (list_map fst e))) ->
    Tot (f (Known x))
  ))
  (f_unknown: (
    (x: value) ->
    (u: squash (list_mem x (list_map snd e) == false)) ->
    Tot (f (Unknown x))
  ))
  (x: maybe_enum_key e)
: Tot (f x)
= match x with
  | Known x' -> f_known x' ()
  | Unknown x' -> f_unknown x' ()

let forall_maybe_enum_key
  (#key #value: eqtype)
  (e: enum key value)
  (f: maybe_enum_key e -> GTot Type0)
  (f_known: squash (list_forallp (fun (x: key) -> list_mem x (list_map fst e) /\ f (Known x)) (list_map fst e)))
  (f_unknown: (
    (x: value) ->
    Tot (squash (list_mem x (list_map snd e) == false ==> f (Unknown x)))
  ))
: Tot (squash (forall (x: maybe_enum_key e) . f x))
= let g
    (x: maybe_enum_key e)
  : Lemma
    (f x)
  = let u : squash (f x) =
      destruct_maybe_enum_key
        e
        (fun y -> squash (f y))
        (fun x' u -> list_forallp_mem (fun (x: key) -> list_mem x (list_map fst e) /\ f (Known x)) (list_map fst e))
        (fun x' u -> f_unknown x') x
    in
    assert (f x)
  in
  Classical.forall_intro g

(* Converting enum keys to their representation, using combinators *)

let enum_repr_of_key'_t
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot Type
= (x: enum_key e) ->
  Tot (r: enum_repr e { r == enum_repr_of_key e x } )

inline_for_extraction
let enum_repr_of_key_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (f : enum_repr_of_key'_t (enum_tail' e))
: Pure (enum_repr_of_key'_t e)
  (requires (Cons? e))
  (ensures (fun _ -> True))
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, r) :: _ ->
     (fun (x: enum_key e) -> (
      if k = x
      then (r <: repr)
      else (f (x <: key) <: repr)
     ) <: (r: enum_repr e { enum_repr_of_key e x == r } )))
     e

inline_for_extraction
let enum_repr_of_key_cons'
  (key repr: eqtype)
  (e: enum key repr)
  (u: unit { Cons? e } )
  (f : enum_repr_of_key'_t (enum_tail' e))
: Tot (enum_repr_of_key'_t e)
= enum_repr_of_key_cons e f

inline_for_extraction
let enum_repr_of_key_cons_nil
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum_repr_of_key'_t e)
  (requires (Cons? e /\ Nil? (enum_tail' e)))
  (ensures (fun _ -> True))
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | [(k, r)] ->
     (fun (x: enum_key e) ->
      (r <: (r: enum_repr e { enum_repr_of_key e x == r } ))))
     e

inline_for_extraction
let enum_repr_of_key_cons_nil'
  (key repr: eqtype)
  (e: enum key repr)
  (u1: unit { Cons? e } )
  (u2: unit { Nil? (enum_tail' e) } )
: Tot (enum_repr_of_key'_t e)
= enum_repr_of_key_cons_nil e

let enum_repr_of_key_append_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (l1: list (key & repr))
  (kr: (key & repr))
  (l2: list (key & repr))
: Lemma
  (requires (e == l1 `L.append` (kr :: l2)))
  (ensures (list_mem (fst kr) (list_map fst e) /\ enum_repr_of_key e (fst kr) == snd kr /\ list_mem (snd kr) (list_map snd e) /\ enum_key_of_repr e (snd kr) == fst kr))
= L.map_append fst l1 (kr :: l2);
  L.noRepeats_append_elim (L.map fst l1) (L.map fst (kr :: l2));
  L.assoc_mem (fst kr) l1;
  L.assoc_mem (fst kr) e;
  L.assoc_append_elim_l (fst kr) l1 (kr :: l2);
  enum_key_of_repr_of_key e (fst kr)


let maybe_enum_key_of_repr'_t
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot Type
= (x: repr) ->
  Tot (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )

#push-options "--z3rlimit 32"

inline_for_extraction
let maybe_enum_key_of_repr'_t_cons_nil
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (maybe_enum_key_of_repr'_t e)
  (requires (Cons? e /\ Nil? (enum_tail' e)))
  (ensures (fun _ -> True))
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
  | [(k, r)] ->
    (fun x -> ((
      if r = x
      then Known k
      else Unknown x
    ) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } ))))
    e

inline_for_extraction
let maybe_enum_key_of_repr'_t_cons_nil'
  (key repr: eqtype)
  (e: enum key repr)
  (u1: unit { Cons? e } )
  (u2: unit { Nil? (enum_tail' e) } )
: Tot (maybe_enum_key_of_repr'_t e)
= maybe_enum_key_of_repr'_t_cons_nil e

inline_for_extraction
let maybe_enum_key_of_repr'_t_cons
  (#key #repr: eqtype)
  (e: enum key repr )
  (g : maybe_enum_key_of_repr'_t (enum_tail' e))
: Pure (maybe_enum_key_of_repr'_t e)
  (requires (Cons? e))
  (ensures (fun _ -> True))
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, r) :: _ ->
     (fun x -> ((
        if r = x
        then Known k
        else
        let y : maybe_enum_key (enum_tail' e) = g x in
        match y with
        | Known k' -> Known (k' <: key)
        | Unknown x' -> Unknown x
      ) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } ))))
      e

inline_for_extraction
let maybe_enum_key_of_repr'_t_cons'
  (key repr: eqtype)
  (e: enum key repr )
  (u: unit { Cons? e } )
  (g : maybe_enum_key_of_repr'_t (enum_tail' e))
: Tot (maybe_enum_key_of_repr'_t e)
= maybe_enum_key_of_repr'_t_cons e g

#pop-options

