module LowParse.SteelST.Fold.SerializationState
open Steel.ST.GenElim
open LowParse.SteelST.Fold.Gen
open LowParse.SteelST.Combinators
open LowParse.SteelST.List.Base

module SZ = LowParse.Steel.StdInt
module H = LowParse.SteelST.Fold.Hoare

(* Step-by-step serialization *)

[@@specialize]
noeq
type state_i_item
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
=
| IParseValue: typ type_of_scalar -> state_i_item type_of_scalar
| IParseList: typ type_of_scalar -> state_i_item type_of_scalar

[@@specialize]
let state_i0
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot Type
= list (state_i_item type_of_scalar)

noeq
type state_t_item
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: state_i_item type_of_scalar -> Type
=
| VParseValue: (t: typ type_of_scalar) -> (v: type_of_typ t) -> state_t_item type_of_scalar (IParseValue t)
| VParseList: (t: typ type_of_scalar) -> (v: list (type_of_typ t)) -> state_t_item type_of_scalar (IParseList t)

noeq
type state_t0
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: state_i0 type_of_scalar -> Type
=
| SNil: state_t0 type_of_scalar []
| SCons:
  (#i: state_i_item type_of_scalar) ->
  (s: state_t_item type_of_scalar i) ->
  (#i': state_i0 type_of_scalar) ->
  (s': state_t0 type_of_scalar i') ->
  state_t0 type_of_scalar (i :: i')

[@@specialize]
let state_i
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot Type
= H.state_i (state_t0 type_of_scalar)

let state_t
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: state_i type_of_scalar -> Type
= H.state_t (state_t0 type_of_scalar)

let spec_write0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (t: typ type_of_scalar)
  (v: type_of_typ t)
: Tot (stt (state_t0 type_of_scalar) unit s (IParseValue t :: s))
= fun st -> ((), SCons (VParseValue t v) st)

let spec_write
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i type_of_scalar)
  (t: typ type_of_scalar)
  (v: type_of_typ t)
: Tot (stt (state_t type_of_scalar) (H.act_ret_t (spec_write0 s.i t v) s.p) s ({ H.i = IParseValue t :: s.i; H.p = H.sem_act_post (spec_write0 s.i t v) s.p }))
= H.sem_act (spec_write0 s.i t v) s.p

let spec_nil0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (t: typ type_of_scalar)
: Tot (stt (state_t0 type_of_scalar) unit s (IParseList t :: s))
= fun st -> ((), SCons (VParseList t []) st)

let spec_nil
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i type_of_scalar)
  (t: typ type_of_scalar)
: Tot (stt (state_t type_of_scalar) (H.act_ret_t (spec_nil0 s.i t) s.p) s ({ H.i = IParseList t :: s.i; H.p = H.sem_act_post (spec_nil0 s.i t) s.p }))
= H.sem_act (spec_nil0 s.i t) s.p

let spec_cons0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (t: typ type_of_scalar)
: Tot (stt (state_t0 type_of_scalar) unit (IParseValue t :: IParseList t :: s) (IParseList t :: s))
= function SCons (VParseValue _ v) (SCons (VParseList _ l) st) -> ((), SCons (VParseList t (v :: l)) st)

let spec_cons
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (t: typ type_of_scalar)
  (ppre: (state_t0 _ (IParseValue t :: IParseList t :: s) -> prop))
: Tot (stt (state_t type_of_scalar) (H.act_ret_t (spec_cons0 s t) ppre) ({ H.i = IParseValue t :: IParseList t :: s; H.p = ppre }) ({ H.i = IParseList t :: s; H.p = H.sem_act_post (spec_cons0 s t) ppre }))
= H.sem_act (spec_cons0 s t) ppre

let spec_list0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (sc: scalar_t)
  (sz: (type_of_scalar sc -> SZ.size_t) { synth_injective sz })
  (t: typ type_of_scalar)
: Tot (stt (state_t0 type_of_scalar) unit (IParseList t :: s) (IParseValue (TList sc sz t) :: s))
= function SCons (VParseList _ l) st -> ((), SCons (VParseValue (TList sc sz t) l) st)

let spec_list
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (sc: scalar_t)
  (sz: (type_of_scalar sc -> SZ.size_t) { synth_injective sz })
  (t: typ type_of_scalar)
  (ppre: (state_t0 _ (IParseList t :: s) -> prop))
: Tot (stt (state_t type_of_scalar) (H.act_ret_t (spec_list0 s sc sz t) ppre) ({ H.i = IParseList t :: s; H.p = ppre }) ({ H.i = IParseValue (TList sc sz t) :: s; H.p = H.sem_act_post (spec_list0 s sc sz t) ppre }))
= H.sem_act (spec_list0 s sc sz t) ppre

let spec_pair0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (t1 t2: typ type_of_scalar)
: Tot (stt (state_t0 type_of_scalar) unit (IParseValue t1 :: IParseValue t2 :: s) (IParseValue (TPair t1 t2) :: s))
= function SCons (VParseValue _ v1) (SCons (VParseValue _ v2) st) -> ((), SCons (VParseValue (TPair t1 t2) (v1, v2)) st)

let spec_pair
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (t1 t2: typ type_of_scalar)
  (ppre: (state_t0 _ (IParseValue t1 :: IParseValue t2 :: s) -> prop))
: Tot (stt (state_t type_of_scalar) (H.act_ret_t (spec_pair0 s t1 t2) ppre) ({ H.i = IParseValue t1 :: IParseValue t2 :: s; H.p = ppre }) ({ H.i = IParseValue (TPair t1 t2) :: s; H.p = H.sem_act_post (spec_pair0 s t1 t2) ppre }))
= H.sem_act (spec_pair0 s t1 t2) ppre

let spec_if0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (t: typ type_of_scalar)
  (b: bool)
  (t1: (squash (b == true) -> typ type_of_scalar))
  (t2: (squash (b == false) -> typ type_of_scalar))
  (sq: squash (t == ifthenelse b t1 t2))
: Tot (stt (state_t0 type_of_scalar) unit (IParseValue t :: s) (IParseValue (TIf b t1 t2) :: s))
= function SCons (VParseValue _ v) st -> ((), SCons (VParseValue (TIf b t1 t2) (coerce _ v)) st)

let spec_choice_post
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (sc: scalar_t)
  (t: typ type_of_scalar)
  (ppre: (state_t0 _ (IParseValue (TScalar sc) :: IParseValue t :: s) -> prop))
  (t': (type_of_scalar sc -> typ type_of_scalar))
  (h': state_t0 _ (IParseValue (TChoice sc t') :: s))
: Tot prop
= exists (h: state_t0 _ (IParseValue (TScalar sc) :: IParseValue t :: s)) .
    ppre h /\
    t == t' (VParseValue?.v (SCons?.s h)) /\
    h' == SCons (VParseValue (TChoice sc t') (mk_choice_value sc (VParseValue?.v (SCons?.s h)) t' (VParseValue?.v (SCons?.s (SCons?.s' h))))) (SCons?.s' (SCons?.s' h))

let spec_choice
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
  (sc: scalar_t)
  (t: typ type_of_scalar)
  (ppre: (state_t0 _ (IParseValue (TScalar sc) :: IParseValue t :: s) -> prop))
  (t': (type_of_scalar sc -> typ type_of_scalar))
  (sq: squash (forall (h: state_t0 _ (IParseValue (TScalar sc) :: IParseValue t :: s)) . ppre h ==> t == t' (VParseValue?.v (SCons?.s h)))) // user proof obligation!
: Tot (stt (state_t type_of_scalar) unit
    ({ H.i = IParseValue (TScalar sc) :: IParseValue t :: s; H.p = ppre })
    ({ H.i = IParseValue (TChoice sc t') :: s; H.p = spec_choice_post s sc t ppre t' })
  )
= function SCons (VParseValue _ tag) (SCons (VParseValue _ value) st) ->
    ((), SCons (VParseValue _ (mk_choice_value sc tag t' value)) st)

let exactly_parses_on
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (s: bytes)
: Tot prop
= match parse p s with
  | None -> False
  | Some (vt, consumed) -> vt == v /\ consumed == Seq.length s

let parsed_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
: GTot (option nat)
= if FStar.StrongExcludedMiddle.strong_excluded_middle (exists b . exactly_parses_on p v b)
  then
    let b = FStar.IndefiniteDescription.indefinite_description_ghost bytes (fun b -> exactly_parses_on p v b) in
    Some (Seq.length b)
  else
    None

let parsed_size_none
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
: Lemma
  (None? (parsed_size p v) <==> (forall b . ~ (exactly_parses_on p v b)))
= ()

let parsed_size_some_intro
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
  (b: bytes)
: Lemma
  (requires (exactly_parses_on p v b))
  (ensures (parsed_size p v == Some (Seq.length b)))
= let b' = FStar.IndefiniteDescription.indefinite_description_ghost bytes (fun b -> exactly_parses_on p v b) in
  parse_injective p b' b

let parsed_size_some_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (v: t)
: Ghost bytes
  (requires (Some? (parsed_size p v)))
  (ensures (fun b ->
    exactly_parses_on p v b /\
    parsed_size p v == Some (Seq.length b)
  ))
= FStar.IndefiniteDescription.indefinite_description_ghost bytes (fun b -> exactly_parses_on p v b)

let type_of_state_i_item
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i_item type_of_scalar)
: Tot Type
= match s with
  | IParseValue t -> type_of_typ t
  | IParseList t -> list (type_of_typ t)

let parser_of_state_i_item
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (s: state_i_item type_of_scalar)
: Tot (parser default_parser_kind (type_of_state_i_item s))
= match s with
  | IParseValue t -> weaken _ (parser_of_typ p_of_s t)
  | IParseList t -> weaken _ (parse_list (parser_of_typ p_of_s t))

let value_of_state_t_item
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (#i: state_i_item type_of_scalar)
  (s: state_t_item type_of_scalar i)
: Tot (type_of_state_i_item i)
= match s with
  | VParseValue _ v -> v
  | VParseList _ v -> v

let size_of_state_t_item
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i_item type_of_scalar)
  (s: state_t_item type_of_scalar i)
: GTot (option nat)
= parsed_size (parser_of_state_i_item p_of_s i) (value_of_state_t_item s)

let option_nat_plus
  (x1 x2: option nat)
: Tot (option nat)
= match x1, x2 with
  | Some v1, Some v2 -> Some (v1 + v2)
  | _ -> None

let option_nat_plus_comm
  (x1 x2: option nat)
: Lemma
  (x1 `option_nat_plus` x2 == x2 `option_nat_plus` x1)
= ()

let option_nat_plus_assoc
  (x1 x2 x3: option nat)
: Lemma
  ((x1 `option_nat_plus` x2) `option_nat_plus` x3 == x1 `option_nat_plus` (x2 `option_nat_plus` x3))
= ()

let option_nat_ge
  (x1 x2: option nat)
: Tot bool
= match x1 with
  | None -> true
  | Some v1 ->
    begin match x2 with
    | None -> false
    | Some v2 -> v1 >= v2
    end

let option_nat_ge_refl
  (x: option nat)
: Lemma
  (option_nat_ge x x)
= ()

let option_nat_ge_trans
  (x1 x2 x3: option nat)
: Lemma
  (requires (x1 `option_nat_ge` x2 /\ x2 `option_nat_ge` x3))
  (ensures (x1 `option_nat_ge` x3))
= ()

let option_nat_ge_plus_inc
  (x1 x2: option nat)
: Lemma
  ((x1 `option_nat_plus` x2) `option_nat_ge` x1)
= ()

let option_nat_ge_plus_compat
  (x1 x2 x: option nat)
: Lemma
  (requires (x1 `option_nat_ge` x2))
  (ensures ((x1 `option_nat_plus` x) `option_nat_ge` (x2 `option_nat_plus` x)))
= ()

let rec size_of_state_t0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
: GTot (option nat)
= match s with
  | SNil -> Some 0
  | SCons s s' -> size_of_state_t_item p_of_s s `option_nat_plus` size_of_state_t0 p_of_s s'

module AP = LowParse.SteelST.ArrayPtr

inline_for_extraction // CRITICAL for extraction
noeq
type ll_state'
: AP.array byte -> Type
= | LNil: (a: AP.v byte) -> squash (AP.length (AP.array_of a) == 0) -> ll_state' (AP.array_of a)
  | LCons: (a0: AP.array byte) -> (a1: AP.array byte) -> (sz1: SZ.size_t) -> (b2: byte_array) -> (a2: AP.array byte) -> squash (AP.merge_into a1 a2 a0 /\ SZ.size_v sz1 == AP.length a1) -> (s2: ll_state' a2) -> ll_state' a0

let rec ll_state'_length
  (#a: AP.array byte)
  (l: ll_state' a)
: Tot nat
  (decreases l)
= match l with
  | LNil _ _ -> 0
  | LCons _ _ _ _ _ _ l' -> 1 + ll_state'_length l'

inline_for_extraction // CRITICAL for extraction
noeq
type ll_state
  (a0: AP.array byte)
= {
    ll_free: AP.v byte;
    ll_b: byte_array;
    ll_a: AP.array byte;
    ll_s: ll_state' ll_a;
    ll_prf: squash (AP.merge_into (AP.array_of ll_free) ll_a a0);
  }

[@@__reduce__]
let ll_state_item_match0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i_item type_of_scalar)
  (s: state_t_item type_of_scalar i)
  (b: byte_array)
  (a: AP.array byte)
: Tot vprop
= exists_ (fun (vb: v _ _) ->
    aparse (parser_of_state_i_item p_of_s i) b vb `star`
    pure (array_of' vb == a /\ vb.contents == value_of_state_t_item s)
  )

let ll_state_item_match
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i_item type_of_scalar)
  (s: state_t_item type_of_scalar i)
  (b: byte_array)
  (a: AP.array byte)
: Tot vprop
= ll_state_item_match0 p_of_s s b a

let rec ll_state_match'
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
  (b: byte_array)
  (a: AP.array byte)
  (ls: ll_state' a)
: Tot vprop
  (decreases ls)
= match ls with
  | LNil vb _ -> AP.arrayptr b vb `star` pure (SNil? s == true)
  | LCons _ a1 _ b' a' _ ls' ->
    begin match s with
    | SNil -> pure False
    | SCons s1 s' -> ll_state_item_match p_of_s s1 b a1 `star` ll_state_match' p_of_s s' b' a' ls'
    end

let elim_ll_state_match'_nil
  (#opened: _)
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
  (b: byte_array)
  (a: AP.array byte)
  (ls: ll_state' a)
: STGhost (squash (LNil? ls /\ Nil? i /\ SNil? s)) opened
    (ll_state_match' p_of_s s b a ls)
    (fun _ ->
      AP.arrayptr b (LNil?.a ls)
    )
    (LNil? ls \/ Nil? i \/ SNil? s)
    (fun _ -> True)
= match ls with
  | LNil _ _ ->
    rewrite
      (ll_state_match' p_of_s s b a ls)
      (AP.arrayptr b (LNil?.a ls) `star` pure (SNil? s == true));
    let _ = gen_elim () in
    ()
  | LCons _ _ _ _ _ _ _ ->
    begin match s with
    | SNil ->
      rewrite
        (ll_state_match' p_of_s s b a ls)
        (pure False);
      let _ = gen_elim () in
      assert False;
      let r : squash (LNil? ls /\ Nil? i /\ SNil? s) = () in
      rewrite // by contradiction
        emp
        (AP.arrayptr b (LNil?.a ls));
      r
    | _ ->
      assert False;
      let r : squash (LNil? ls /\ Nil? i /\ SNil? s) = () in
      rewrite // by contradiction
        (ll_state_match' p_of_s s b a ls)
        (AP.arrayptr b (LNil?.a ls));
      r
    end

let elim_ll_state_match'_cons
  (#opened: _)
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
  (b: byte_array)
  (a: AP.array byte)
  (ls: ll_state' a)
: STGhost (squash (LCons? ls /\ Cons? i /\ SCons? s)) opened
    (ll_state_match' p_of_s s b a ls)
    (fun _ ->
      ll_state_item_match p_of_s (SCons?.s s) b (LCons?.a1 ls) `star`
      ll_state_match' p_of_s (SCons?.s' s) (LCons?.b2 ls) (LCons?.a2 ls) (LCons?.s2 ls)
    )
    (LCons? ls \/ Cons? i \/ SCons? s)
    (fun _ -> True)
= match ls with
  | LNil vb _ ->
    rewrite
      (ll_state_match' p_of_s s b a ls)
      (AP.arrayptr b vb `star` pure (SNil? s == true));
    let _ = gen_elim () in
    assert False;
    let r : squash (LCons? ls /\ Cons? i /\ SCons? s) = () in
    rewrite // by contradiction
      (AP.arrayptr b vb)
      (ll_state_item_match p_of_s (SCons?.s s) b (LCons?.a1 ls) `star`
        ll_state_match' p_of_s (SCons?.s' s) (LCons?.b2 ls) (LCons?.a2 ls) (LCons?.s2 ls));
    r
  | LCons _ _ _ _ _ _ _ ->
    begin match s with
    | SNil ->
      rewrite
        (ll_state_match' p_of_s s b a ls)
        (pure False);
      let _ = gen_elim () in
      assert False;
      let r : squash (LCons? ls /\ Cons? i /\ SCons? s) = () in
      rewrite // by contradiction
        emp
        (ll_state_item_match p_of_s (SCons?.s s) b (LCons?.a1 ls) `star`
          ll_state_match' p_of_s (SCons?.s' s) (LCons?.b2 ls) (LCons?.a2 ls) (LCons?.s2 ls));
      r
    | _ ->
      let r : squash (LCons? ls /\ Cons? i /\ SCons? s) = () in
      rewrite
        (ll_state_match' p_of_s s b a ls)
        (ll_state_item_match p_of_s (SCons?.s s) b (LCons?.a1 ls) `star`
          ll_state_match' p_of_s (SCons?.s' s) (LCons?.b2 ls) (LCons?.a2 ls) (LCons?.s2 ls));
      r
    end

module R = Steel.ST.Reference

[@@__reduce__]
let ll_state_match0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
  (ls: ll_state a)
: Tot vprop
= exists_ (fun sz ->
    R.pts_to b_sz full_perm sz `star`
    AP.arrayptr b ls.ll_free `star`
    ll_state_match' p_of_s s ls.ll_b ls.ll_a ls.ll_s `star`
    pure (SZ.size_v sz == AP.length (AP.array_of ls.ll_free) /\ AP.array_perm (AP.array_of ls.ll_free) == full_perm)
  )

let ll_state_match
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
  (ls: ll_state a)
: Tot vprop
= ll_state_match0 p_of_s b b_sz a s ls

[@@__reduce__]
let ll_state_failure0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
: Tot vprop
= exists_ (fun vb -> exists_ (fun sz ->
    AP.arrayptr b vb `star`
    R.pts_to b_sz full_perm sz `star`
    pure (AP.array_of vb == a /\ size_of_state_t0 p_of_s s `option_nat_ge` Some (AP.length a + 1))
  ))

let ll_state_failure
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
= ll_state_failure0 p_of_s b b_sz a s

let state_ge
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i1: state_i0 type_of_scalar)
  (s1: state_t0 type_of_scalar i1)
  (#i2: state_i0 type_of_scalar)
  (s2: state_t0 type_of_scalar i2)
: Tot prop
= (size_of_state_t0 p_of_s s1 `option_nat_ge` size_of_state_t0 p_of_s s2) == true

let ll_state_shape'
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (i: state_i0 type_of_scalar)
  (#a0: AP.array byte)
  (ls: ll_state' a0)
: Tot prop
= ll_state'_length ls == List.Tot.length i

let ll_state_shape
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
  (a0: AP.array byte)
  (i: state_i0 type_of_scalar)
  (l: ll_state a0)
: Tot prop
= ll_state_shape' i l.ll_s

let rec ll_state_match'_shape
  (#opened: _)
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
  (b: byte_array)
  (a: AP.array byte)
  (ls: ll_state' a)
: STGhost unit opened
    (ll_state_match' p_of_s s b a ls)
    (fun _ -> ll_state_match' p_of_s s b a ls)
    True
    (fun _ -> ll_state_shape' i ls)
    (decreases ls)
= match ls with
  | LNil vb _ ->
    rewrite
      (ll_state_match' p_of_s s b a ls)
      (AP.arrayptr b vb `star` pure (SNil? s == true));
    let _ = gen_elim () in
     rewrite
      (AP.arrayptr b vb `star` pure (SNil? s == true))
      (ll_state_match' p_of_s s b a ls)
  | LCons _ a1 _ b' a' _ ls' ->
    begin match s with
    | SNil ->
      rewrite
        (ll_state_match' p_of_s s b a ls)
        (pure False);
      let _ = gen_elim () in
      rewrite // by contradiction
        emp
        (ll_state_match' p_of_s s b a ls)
    | SCons s1 s' ->
      rewrite
        (ll_state_match' p_of_s s b a ls)
        (ll_state_item_match p_of_s s1 b a1 `star` ll_state_match' p_of_s s' b' a' ls');
      ll_state_match'_shape p_of_s s' b' a' ls';
      rewrite
        (ll_state_item_match p_of_s s1 b a1 `star` ll_state_match' p_of_s s' b' a' ls')
        (ll_state_match' p_of_s s b a ls)
    end

let rec wipe_ll_state_match' // necessary in case of failure. This also explains why I need the byte_array available outside of ll_state'
  (#opened: _)
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
  (b: byte_array)
  (a: AP.array byte)
  (ls: ll_state' a)
: STGhost (AP.v byte) opened
    (ll_state_match' p_of_s s b a ls)
    (fun vb -> AP.arrayptr b vb)
    True
    (fun vb -> AP.array_of vb == a)
= match ls with
  | LNil vb _ ->
    rewrite
      (ll_state_match' p_of_s s b a ls)
      (AP.arrayptr b vb `star` pure (SNil? s == true));
    let _ = gen_elim () in
    vb
  | LCons _ a1 _ b' a' _ ls' ->
    begin match s with
    | SNil ->
      rewrite
        (ll_state_match' p_of_s s b a ls)
        (pure False);
      let _ = gen_elim () in
      let vb : AP.v byte = false_elim () in
      rewrite
        emp
        (AP.arrayptr b vb);
      vb
    | SCons s1 s' -> 
      rewrite
        (ll_state_match' p_of_s s b a ls)
        (ll_state_item_match p_of_s s1 b a1 `star` ll_state_match' p_of_s s' b' a' ls');
      let _ = wipe_ll_state_match' p_of_s s' b' a' ls' in
      rewrite
        (ll_state_item_match p_of_s s1 b a1)
        (ll_state_item_match0 p_of_s s1 b a1);
      let _ = gen_elim () in
      let _ = elim_aparse _ b in
      AP.join b b'
    end

let wipe_ll_state_match0
  (#opened: _)
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (#i: state_i0 type_of_scalar)
  (s: state_t0 type_of_scalar i)
  (ls: ll_state a)
: STGhost (AP.v byte) opened
    (ll_state_match p_of_s b b_sz a s ls)
    (fun vb -> AP.arrayptr b vb `star` exists_ (R.pts_to b_sz full_perm))
    True
    (fun vb -> AP.array_of vb == a)
= rewrite
    (ll_state_match p_of_s b b_sz a s ls)
    (ll_state_match0 p_of_s b b_sz a s ls);
  let _ = gen_elim () in
  let _ = wipe_ll_state_match' p_of_s _ _ _ _ in
  AP.join b _

inline_for_extraction
let ll_state_ptr' = list (R.ref SZ.size_t & R.ref byte_array)

inline_for_extraction
let ll_state_ptr = (R.ref byte_array & ll_state_ptr')

inline_for_extraction
let fstx
  (#t1 #t2: Type)
  (x: (t1 & t2))
: Tot t1
= match x with (x, _) -> x

inline_for_extraction
let sndx
  (#t1 #t2: Type)
  (x: (t1 & t2))
: Tot t2
= match x with (_, x) -> x

inline_for_extraction
let list_hd
  (#t: Type)
  (l: list t { Cons? l })
: Tot t
= match l with Cons a _ -> a

inline_for_extraction
let list_tl
  (#t: Type)
  (l: list t { Cons? l })
: Tot (list t)
= match l with Cons _ l' -> l'

#set-options "--ide_id_info_off"

let rec ll_state_pts_to'
  (#a: AP.array byte)
  (lsp: ll_state_ptr')
  (ls: ll_state' a)
: Tot vprop
  (decreases ls)
= match ls with
  | LNil _ _ -> pure (Nil? lsp == true)
  | LCons _ a1 sz1 b' a' _ ls' ->
    begin match lsp with
    | [] -> pure False
    | x :: l' -> R.pts_to (fstx x) full_perm sz1 `star` R.pts_to (sndx x) full_perm b' `star` ll_state_pts_to' l' ls'
    end

let elim_ll_state_pts_to'_nil
  (#opened: _)
  (#a: AP.array byte)
  (lsp: ll_state_ptr')
  (ls: ll_state' a)
: STGhost unit opened
    (ll_state_pts_to' lsp ls)
    (fun _ -> emp)
    (LNil? ls \/ Nil? lsp)
    (fun _ -> LNil? ls /\ Nil? lsp)
= if LNil? ls
  then begin
    rewrite (ll_state_pts_to' lsp ls) (pure (Nil? lsp == true));
    let _ = gen_elim () in
    ()
  end else
    match lsp with
    | [] ->
      rewrite (ll_state_pts_to' lsp ls) (pure False);
      let _ = gen_elim () in
      ()
    | _ ->
      assert False;
      rewrite (ll_state_pts_to' lsp ls) emp

let elim_ll_state_pts_to'_cons
  (#opened: _)
  (#a: AP.array byte)
  (lsp: ll_state_ptr')
  (ls: ll_state' a)
: STGhost (squash (LCons? ls /\ Cons? lsp)) opened
    (ll_state_pts_to' lsp ls)
    (fun _ -> R.pts_to (fstx (list_hd lsp)) full_perm (LCons?.sz1 ls) `star` R.pts_to (sndx (list_hd lsp)) full_perm (LCons?.b2 ls) `star` ll_state_pts_to' (list_tl lsp) (LCons?.s2 ls))
    (LCons? ls \/ Cons? lsp)
    (fun _ -> True)
= if LNil? ls
  then begin
    rewrite
      (ll_state_pts_to' lsp ls)
      (pure (Nil? lsp == true));
    let _ = gen_elim () in
    assert False;
    rewrite
      emp
      (R.pts_to (fstx (list_hd lsp)) full_perm (LCons?.sz1 ls) `star` R.pts_to (sndx (list_hd lsp)) full_perm (LCons?.b2 ls) `star` ll_state_pts_to' (list_tl lsp) (LCons?.s2 ls))
  end else
    match lsp with
    | [] ->
      rewrite
        (ll_state_pts_to' lsp ls)
        (pure False);
      let _ = gen_elim () in
      assert False;
      rewrite
        emp
        (R.pts_to (fstx (list_hd lsp)) full_perm (LCons?.sz1 ls) `star` R.pts_to (sndx (list_hd lsp)) full_perm (LCons?.b2 ls) `star` ll_state_pts_to' (list_tl lsp) (LCons?.s2 ls))
    | _ ->
      rewrite
        (ll_state_pts_to' lsp ls)
        (R.pts_to (fstx (list_hd lsp)) full_perm (LCons?.sz1 ls) `star` R.pts_to (sndx (list_hd lsp)) full_perm (LCons?.b2 ls) `star` ll_state_pts_to' (list_tl lsp) (LCons?.s2 ls))

[@@__reduce__]
let ll_state_pts_to0
  (a: AP.array byte)
  (lsp: ll_state_ptr)
  (ls: ll_state a)
: Tot vprop
= R.pts_to (fstx lsp) full_perm ls.ll_b `star` ll_state_pts_to' (sndx lsp) ls.ll_s

let ll_state_pts_to
  (a: AP.array byte)
  (lsp: ll_state_ptr)
  (ls: ll_state a)
: Tot vprop
= ll_state_pts_to0 a lsp ls

let cl0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
: Tot (low_level_state (state_i0 type_of_scalar) (state_t0 type_of_scalar) (ll_state a) ll_state_ptr)
= {
    ll_state_match = ll_state_match p_of_s b b_sz a;
    ll_state_failure = ll_state_failure p_of_s b b_sz a;
    state_ge = state_ge p_of_s;
    state_ge_refl = (fun _ -> ());
    state_ge_trans = (fun _ _ _ -> ());
    ll_state_failure_inc = (fun #_ #i1 s1 #i2 s2 ->
      rewrite
        (ll_state_failure p_of_s b b_sz a #i1 s1)
        (ll_state_failure0 p_of_s b b_sz a #i1 s1);
      let _ = gen_elim () in
      rewrite
        (ll_state_failure0 p_of_s b b_sz a #i2 s2)
        (ll_state_failure p_of_s b b_sz a #i2 s2)
    );
    ll_state_shape = ll_state_shape type_of_scalar a;
    ll_state_match_shape = (fun #_ #i h l ->
      rewrite
        (ll_state_match p_of_s b b_sz a #i h l)
        (ll_state_match0 p_of_s b b_sz a #i h l);
      let _ = gen_elim () in
      ll_state_match'_shape p_of_s _ _ _ _;
      rewrite
        (ll_state_match0 p_of_s b b_sz a #i h l)
        (ll_state_match p_of_s b b_sz a #i h l)
    );
    ll_state_pts_to = ll_state_pts_to a;
  }

let cl
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
: Tot (low_level_state (state_i type_of_scalar) (state_t type_of_scalar) (ll_state a) ll_state_ptr)
= H.cl (cl0 p_of_s b b_sz a)

let wipe_ll_state_match
  (#opened: _)
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (#i: state_i type_of_scalar)
  (s: state_t type_of_scalar i)
  (ls: ll_state a)
: STGhost (AP.v byte) opened
    ((cl p_of_s b b_sz a).ll_state_match s ls)
    (fun vb -> AP.arrayptr b vb `star` exists_ (R.pts_to b_sz full_perm))
    True
    (fun vb -> AP.array_of vb == a)
= rewrite
    ((cl p_of_s b b_sz a).ll_state_match s ls)
    (ll_state_match p_of_s b b_sz a #i.i s ls);
  wipe_ll_state_match0 p_of_s b b_sz a _ _

let initial_index0
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot (state_i0 type_of_scalar)
= []

let initial_state0
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot (state_t0 type_of_scalar (initial_index0 type_of_scalar))
= SNil

let initial_state_unique
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
  (s: state_t0 type_of_scalar (initial_index0 type_of_scalar))
: Lemma
  (s == initial_state0 type_of_scalar)
= ()

inline_for_extraction
let mk_initial_state0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (vb: AP.v byte)
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
: Tot (mk_ll_state_t
    (cl0 p_of_s b b_sz (AP.array_of vb))
    (AP.arrayptr b vb `star`
      (exists_ (fun sz ->
        R.pts_to b_sz full_perm sz `star`
        pure (SZ.size_v sz == AP.length (AP.array_of vb) /\ AP.array_perm (AP.array_of vb) == full_perm)
    )))
    (initial_state0 type_of_scalar)
  )
= fun k ->
  let _ = gen_elim () in
  let sz = read_replace b_sz in
  let bz = AP.split b sz in
  let _ = gen_elim () in
  let ll_free = vpattern_replace (AP.arrayptr b) in
  let vbz = vpattern_replace (AP.arrayptr bz) in
  [@inline_let] // CRITICAL for extraction
  let pb : ll_state (AP.array_of vb) = {
    ll_free = ll_free;
    ll_b = bz;
    ll_a = AP.array_of vbz;
    ll_s = LNil vbz ();
    ll_prf = ();
  }
  in
  rewrite
    (AP.arrayptr b _)
    (AP.arrayptr b pb.ll_free);
  rewrite
    (AP.arrayptr bz _ `star` pure (SNil? (initial_state0 type_of_scalar) == true))
    (ll_state_match' p_of_s (initial_state0 type_of_scalar) pb.ll_b pb.ll_a pb.ll_s);
  rewrite
    (ll_state_match0 p_of_s b b_sz (AP.array_of vb) (initial_state0 type_of_scalar) pb)
    ((cl0 p_of_s b b_sz (AP.array_of vb)).ll_state_match (initial_state0 type_of_scalar) pb);
  k _

[@@specialize]
let initial_index
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot (state_i type_of_scalar)
= { H.i = initial_index0 type_of_scalar; H.p = (fun h' -> h' == initial_state0 type_of_scalar)}

let initial_state
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot (state_t type_of_scalar (initial_index type_of_scalar))
= initial_state0 type_of_scalar

inline_for_extraction
let mk_initial_state
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (vb: AP.v byte)
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
: Tot (mk_ll_state_t
    (cl p_of_s b b_sz (AP.array_of vb))
    (AP.arrayptr b vb `star`
      (exists_ (fun sz ->
        R.pts_to b_sz full_perm sz `star`
        pure (SZ.size_v sz == AP.length (AP.array_of vb))
    )))
    (initial_state type_of_scalar)
  )
= coerce _ (H.mk_ll_state_eq (mk_initial_state0 p_of_s vb b b_sz))

// NOTE: I could very well implement this with exists_ as a
// pre-resource, leveraging hop_arrayptr_aparse, but I can't make
// sense of this scenario

inline_for_extraction
let elim_ll_state_match_final0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (t: Ghost.erased (state_i_item type_of_scalar))
  (i: Ghost.erased (state_i0 type_of_scalar))
  (s: Ghost.erased (state_t0 type_of_scalar i))
  (ls: ll_state a)
: ST byte_array
    ((cl0 p_of_s b b_sz a).ll_state_match s ls)
    (fun b' -> exists_ (fun vb -> exists_ (fun sz -> exists_ (fun (vb': v default_parser_kind (type_of_state_i_item t)) ->
      AP.arrayptr b vb `star`
      R.pts_to b_sz full_perm sz `star`
      aparse (parser_of_state_i_item p_of_s t) b' vb' `star` pure (
      SZ.size_v sz == AP.length (AP.array_of vb) /\
      Ghost.reveal i == [Ghost.reveal t] /\
      vb'.contents == value_of_state_t_item (SCons?.s s) /\
      AP.merge_into (AP.array_of vb) (array_of' vb') a
    )))))
    (Ghost.reveal i == [Ghost.reveal t])
    (fun _ -> True)
= rewrite
    ((cl0 p_of_s b b_sz a).ll_state_match s ls)
    (ll_state_match0 p_of_s b b_sz a s ls);
  let _ = gen_elim () in
  let _ = elim_ll_state_match'_cons p_of_s _ _ _ _ in
  let _ = elim_ll_state_match'_nil p_of_s _ _ _ _ in
  rewrite
    (ll_state_item_match p_of_s (SCons?.s s) _ _)
    (ll_state_item_match0 p_of_s (SCons?.s s) ls.ll_b (LCons?.a1 ls.ll_s));
  let _ = gen_elim () in
  let vbl = elim_aparse _ ls.ll_b in
  let vbz = vpattern_replace (fun vbz -> AP.arrayptr ls.ll_b _ `star` AP.arrayptr _ vbz) in
  assert (AP.contents_of' vbz `Seq.equal` Seq.empty);
  Seq.append_empty_r (AP.contents_of' vbl);
  let _ = AP.join #_ #_ #_ #vbz ls.ll_b _ in
  let _ = intro_aparse (parser_of_state_i_item p_of_s t) ls.ll_b in
  return ls.ll_b

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
let elim_ll_state_match_final
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (t: Ghost.erased (state_i_item type_of_scalar))
  (i: Ghost.erased (state_i type_of_scalar))
  (s: Ghost.erased (state_t type_of_scalar i))
  (ls: ll_state a)
: ST byte_array
    ((cl p_of_s b b_sz a).ll_state_match s ls)
    (fun b' -> exists_ (fun vb -> exists_ (fun sz -> exists_ (fun (vb': v default_parser_kind (type_of_state_i_item t)) ->
      AP.arrayptr b vb `star`
      R.pts_to b_sz full_perm sz `star`
      aparse (parser_of_state_i_item p_of_s t) b' vb' `star` pure (
      SZ.size_v sz == AP.length (AP.array_of vb) /\
      (Ghost.reveal i).i == [Ghost.reveal t] /\
      vb'.contents == value_of_state_t_item (SCons?.s s) /\
      AP.merge_into (AP.array_of vb) (array_of' vb') a
    )))))
    ((Ghost.reveal i).i == [Ghost.reveal t])
    (fun _ -> True)
=
  let s0 : Ghost.erased (state_t0 type_of_scalar i.H.i) = Ghost.hide (Ghost.reveal s) in
  rewrite
    ((cl p_of_s b b_sz a).ll_state_match s ls)
    ((cl0 p_of_s b b_sz a).ll_state_match s0 ls);
  let res = elim_ll_state_match_final0 p_of_s b b_sz a t (i.H.i) s0 ls in
  let _ = gen_elim () in
  return res

#pop-options

inline_for_extraction
let with_ll_state_ptr'_t
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (i: state_i0 type_of_scalar)
: Tot Type
= (a: AP.array byte) ->
  (l: ll_state' a) ->
  (#kpre: vprop) ->
  (#t: Type) ->
  (#kpost: (t -> vprop)) ->
  (k: (
    (p: ll_state_ptr') ->
    STT t
      (kpre `star` ll_state_pts_to' p l)
      (fun r -> kpost r `star` exists_ (fun a' -> exists_ (ll_state_pts_to' #a' p)))
  )) ->
  STF t kpre kpost (ll_state_shape' i l) (fun _ -> True)

inline_for_extraction
let with_ll_state_ptr0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (i: Ghost.erased (state_i0 type_of_scalar))
  (w: with_ll_state_ptr'_t i)
: Tot (with_ll_state_ptr_t (cl0 p_of_s b b_sz a) i)
= fun l k ->
    w _ l.ll_s (fun p' ->
      with_local l.ll_b (fun pb ->
        [@inline_let]
        let p : ll_state_ptr = (pb, p') in
        rewrite
          (R.pts_to pb full_perm _ `star` ll_state_pts_to' _ _)
          (ll_state_pts_to a p l);
        let res = k _ in
        let l' = elim_exists () in
        rewrite
          (ll_state_pts_to a p l')
          (ll_state_pts_to0 a p l');
        vpattern_rewrite (fun b -> R.pts_to b _ _) pb;
        vpattern_rewrite (fun p' -> ll_state_pts_to' p' _) p';
        return res
      )
    )

inline_for_extraction
let with_ll_state_ptr'_nil
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot (with_ll_state_ptr'_t #_ #type_of_scalar [])
= fun a l k ->
    [@inline_let]
    let pl : ll_state_ptr' = [] in
    noop ();
    rewrite (pure (Nil? pl == true)) (ll_state_pts_to' pl l);
    let res = k _ in
    let _ = gen_elim () in
    elim_ll_state_pts_to'_nil _ _;
    return res

inline_for_extraction
let with_ll_state_ptr'_cons
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: Ghost.erased (state_i_item type_of_scalar))
  (s': Ghost.erased (state_i0 type_of_scalar))
  (w: with_ll_state_ptr'_t (Ghost.reveal s'))
: Tot (with_ll_state_ptr'_t (Ghost.reveal s :: Ghost.reveal s'))
= fun a l k ->
    with_local (LCons?.sz1 l) (fun bsz ->
    with_local (LCons?.b2 l) (fun bb ->
    w _ (LCons?.s2 l) (fun bs' ->
      [@inline_let]
      let bs : ll_state_ptr' = (bsz, bb) :: bs' in
      rewrite (R.pts_to bsz _ _ `star` R.pts_to bb _ _ `star` ll_state_pts_to' _ _) (ll_state_pts_to' bs l);
      let res = k _ in
      let a' = elim_exists () in
      let l' = elim_exists () in
      let _ = elim_ll_state_pts_to'_cons _ _ in
      vpattern_rewrite (fun x -> R.pts_to #SZ.size_t x _ _) bsz;
      vpattern_rewrite (fun x -> R.pts_to #byte_array x _ _) bb;
      vpattern_rewrite (fun x -> ll_state_pts_to' x _) bs';
      return res
    )))

[@@specialize]
let rec with_ll_state_ptr'
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
: Tot (with_ll_state_ptr'_t s)
  (decreases s)
= match s with
  | [] -> with_ll_state_ptr'_nil type_of_scalar
  | s :: s' -> with_ll_state_ptr'_cons s s' (with_ll_state_ptr' s')

inline_for_extraction
let load_ll_state_ptr'_t
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (i: state_i0 type_of_scalar)
: Tot Type
=
  (#a: AP.array byte) ->
  (#gl: Ghost.erased (ll_state' a)) ->
  (p: ll_state_ptr') ->
  (#kpre: vprop) ->
  (#t: Type) ->
  (#kpost: (t -> vprop)) ->
  (k: (
    (l: ll_state' a) ->
    ST t
       (kpre `star` ll_state_pts_to' p l)
       kpost
       (l == Ghost.reveal gl)
       (fun _ -> True)
  )) ->
  STF t
    (kpre `star` ll_state_pts_to' p gl)
    kpost
    (ll_state_shape' i gl)
    (fun _ -> True)

inline_for_extraction
let load_ll_state_ptr0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (i: Ghost.erased (state_i0 type_of_scalar))
  (w: load_ll_state_ptr'_t i)
: Tot (load_ll_state_ptr_t (cl0 p_of_s b b_sz a) i)
= fun #gl p k ->
  rewrite
    ((cl0 p_of_s b b_sz a).ll_state_pts_to p gl)
    (ll_state_pts_to0 a p gl);
  let b1 = read_replace (fstx p) in
  w (sndx p) (fun l' ->
    [@inline_let]
    let l : ll_state a = {
      ll_free = gl.ll_free;
      ll_b = b1;
      ll_a = gl.ll_a;
      ll_s = l';
      ll_prf = ();
    }
    in
    rewrite
      (R.pts_to _ _ _ `star` ll_state_pts_to' _ _)
      ((cl0 p_of_s b b_sz a).ll_state_pts_to p l);
    k _
  )

inline_for_extraction
let load_ll_state_ptr'_nil
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot (load_ll_state_ptr'_t #_ #type_of_scalar [])
= fun #a #gl p k ->
    let _ = elim_ll_state_pts_to'_nil _ _ in
    [@inline_let]
    let l : ll_state' a = LNil (LNil?.a gl) () in
    rewrite
      (pure (Nil? p == true))
      (ll_state_pts_to' p l);
    k _

inline_for_extraction
let load_ll_state_ptr'_cons
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: Ghost.erased (state_i_item type_of_scalar))
  (s': Ghost.erased (state_i0 type_of_scalar))
  (w: load_ll_state_ptr'_t (Ghost.reveal s'))
: Tot (load_ll_state_ptr'_t (Ghost.reveal s :: Ghost.reveal s'))
= fun #a #gl p k ->
    let _ = elim_ll_state_pts_to'_cons _ _ in
    let sz1 = R.read #SZ.size_t _ in
    let b2 = R.read #byte_array _ in
    w _ (fun l' ->
      [@inline_let]
      let l : ll_state' a = LCons a (LCons?.a1 gl) sz1 b2 (LCons?.a2 gl) () l' in
      rewrite
        (R.pts_to #SZ.size_t _ _ _ `star` R.pts_to #byte_array _ _ _ `star` ll_state_pts_to' _ _)
        (ll_state_pts_to' p l);
      k _
    )

[@@specialize]
let rec load_ll_state_ptr'
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
: Tot (load_ll_state_ptr'_t s)
  (decreases s)
= match s with
  | [] -> load_ll_state_ptr'_nil type_of_scalar
  | s :: s' -> load_ll_state_ptr'_cons s s' (load_ll_state_ptr' s')

inline_for_extraction
let store_ll_state_ptr'_t
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (i: state_i0 type_of_scalar)
: Tot Type
= (#a: AP.array byte) ->
  (#gl: Ghost.erased (ll_state' a)) ->
  (p: ll_state_ptr') ->
  (#a': AP.array byte) ->
  (l': ll_state' a') ->
  ST unit
     (ll_state_pts_to' p gl)
     (fun _ -> ll_state_pts_to' p l')
     (ll_state_shape' i gl /\ ll_state_shape' i l')
     (fun _ -> True)

inline_for_extraction
let store_ll_state_ptr0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
  (i: Ghost.erased (state_i0 type_of_scalar))
  (w: store_ll_state_ptr'_t i)
: Tot (store_ll_state_ptr_t (cl0 p_of_s b b_sz a) i)
= fun #gl p l ->
    rewrite
      ((cl0 p_of_s b b_sz a).ll_state_pts_to p gl)
      (ll_state_pts_to0 a p gl);
    R.write _ l.ll_b;
    w _ l.ll_s;
    rewrite
      (R.pts_to _ _ _ `star` ll_state_pts_to' _ _)
      ((cl0 p_of_s b b_sz a).ll_state_pts_to p l)

inline_for_extraction
let store_ll_state_ptr'_nil
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
: Tot (store_ll_state_ptr'_t #_ #type_of_scalar [])
= fun #a #gl p l ->
    let _ = elim_ll_state_pts_to'_nil _ _ in
    rewrite
      (pure (Nil? p == true))
      (ll_state_pts_to' p l)

inline_for_extraction
let store_ll_state_ptr'_cons
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: Ghost.erased (state_i_item type_of_scalar))
  (s': Ghost.erased (state_i0 type_of_scalar))
  (w: store_ll_state_ptr'_t (Ghost.reveal s'))
: Tot (store_ll_state_ptr'_t (Ghost.reveal s :: Ghost.reveal s'))
= fun #a #gl p l ->
    let _ = elim_ll_state_pts_to'_cons _ _ in
    R.write _ (LCons?.sz1 l);
    R.write _ (LCons?.b2 l);
    w _ (LCons?.s2 l);
    rewrite
      (R.pts_to #SZ.size_t _ _ _ `star` R.pts_to #byte_array _ _ _ `star` ll_state_pts_to' _ _)
      (ll_state_pts_to' p l)

[@@specialize]
let rec store_ll_state_ptr'
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: state_i0 type_of_scalar)
: Tot (store_ll_state_ptr'_t s)
  (decreases s)
= match s with
  | [] -> store_ll_state_ptr'_nil type_of_scalar
  | s :: s' -> store_ll_state_ptr'_cons s s' (store_ll_state_ptr' s')

[@@specialize]
let ptr_cl0
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
: Tot (ll_state_ptr_ops (cl0 p_of_s b b_sz a))
= {
    with_ll_state_ptr = (fun (i: state_i0 type_of_scalar) -> with_ll_state_ptr0 p_of_s b b_sz a i (with_ll_state_ptr' i));
    load_ll_state_ptr = (fun i -> load_ll_state_ptr0 p_of_s b b_sz a i (load_ll_state_ptr' i));
    store_ll_state_ptr = (fun i -> store_ll_state_ptr0 p_of_s b b_sz a i (store_ll_state_ptr' i));
  }

[@@specialize]
let ptr_cl
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (p_of_s: ((s: scalar_t) -> scalar_ops (type_of_scalar s)))
  (b: byte_array)
  (b_sz: R.ref SZ.size_t)
  (a: AP.array byte)
: Tot (ll_state_ptr_ops (cl p_of_s b b_sz a))
= H.ptr_cl (ptr_cl0 p_of_s b b_sz a)

