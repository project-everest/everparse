module LowParse.Spec.Fold

module U8 = FStar.UInt8

noeq
type typ =
| TU8
| TPair: typ -> typ -> typ
| TList: (elt: typ) -> typ
| TChoice: (bool -> typ) -> typ

let rec type_of_typ (t: typ) : Tot Type0 = match t with
| TU8 -> U8.t
| TPair t1 t2 -> (type_of_typ t1 & type_of_typ t2)
| TList t' -> list (type_of_typ t') // we ignore the serializer for now
| TChoice f -> (x: bool & type_of_typ (f x)) 

open LowParse.Spec.Int
open LowParse.Spec.List
open LowParse.Spec.VLData

let pkind = {
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let parse_bool : parser _ bool =
  LowParse.Spec.Enum.parse_enum_key parse_u8 [(true, 1uy); (false, 0uy)]
  `parse_synth`
  (fun x -> x <: bool)

let rec parser_of_typ (t: typ) : Tot (parser pkind (type_of_typ t)) =
  match t returns parser pkind (type_of_typ t) with
  | TU8 -> weaken _ parse_u8
  | TPair t1 t2 -> nondep_then (parser_of_typ t1) (parser_of_typ t2)
  | TList t' ->
    weaken _ (parse_vldata 1 (parse_list (parser_of_typ t')))
  | TChoice f -> weaken _ (parse_dtuple2 parse_bool (fun x -> parser_of_typ (f x)))

let stt (state_t: Type) (ret_t: Type) (pre: state_t -> prop) (post: state_t -> ret_t -> state_t -> prop) : Tot Type = (x: state_t) -> Pure (ret_t & state_t)
  (pre x)
  (fun (r, y) -> post x r y)

let ret (#state_t: Type) (#ret_t: Type) (x: ret_t) : Tot (stt state_t ret_t (fun _ -> True) (fun s x' s' -> s == s' /\ x == x')) = fun s -> (x, s)

let get (#state_t: Type) () : Tot (stt state_t (Ghost.erased state_t) (fun _ -> True) (fun s x' s' -> s == s' /\ s == Ghost.reveal x')) = fun s -> (Ghost.hide s, s)

let skip (#state_t: Type) () : Tot (stt state_t unit (fun _ -> True) (fun _ _ _ -> True)) = ret ()

let state_assert (#state_t: Type) (p: state_t -> prop) : Tot (stt state_t unit p (fun s _ s' -> s == s' /\ p s)) = fun s -> ((), s)

let bind (#state_t: Type) (#ret1_t #ret2_t: Type)
  (#pre1: state_t -> prop)
  (#post1: state_t -> ret1_t -> state_t -> prop)
  (f1: stt state_t ret1_t pre1 post1)
  (#pre2: state_t -> prop)
  (#post2: state_t -> ret2_t -> state_t -> prop)
  (f2: (r1: ret1_t) -> stt state_t ret2_t pre2 post2)
: Pure (stt state_t ret2_t pre1 (fun s0 r2 s2 -> exists r1 s1 .
    post1 s0 r1 s1 /\
    pre2 s1 /\
    post2 s1 r2 s2
  ))
  (requires (forall s0 r1 s1 . post1 s0 r1 s1 ==> pre2 s1))
  (ensures (fun _ -> True))
= fun state0 ->
    let (r1, state1) = f1 state0 in
    let (r2, state2) = f2 r1 state1 in
    (r2, state2)

let weaken (#state_t: Type) (pre: state_t -> prop) (post: state_t -> prop) : Pure (stt state_t unit pre (fun _ _ -> post)) (requires (forall s . pre s ==> post s)) (ensures (fun _ -> True)) =
  fun s -> ((), s)

let fold_t (state_t: Type) (t: Type) (ret_t: Type) (pre: state_t -> prop) (post: t -> state_t -> ret_t -> state_t -> prop) : Tot Type = ((v: t) -> stt state_t ret_t pre (post v))

let fold_pair_post
  (#state_t: Type)
  #t1 #ret1
  (pre1: state_t -> prop)
  (post1: t1 -> state_t -> ret1 -> state_t -> prop)
  #t2 #ret2
  (pre2: ret1 -> state_t -> prop)
  (post2: (x: ret1) -> t2 -> state_t -> ret2 -> state_t -> prop)
  (v: (t1 & t2))
  (s0: state_t)
  (r2: ret2)
  (s2: state_t)
: Tot prop
= pre1 s0 /\ (exists s1 r1 . post1 (fst v) s0 r1 s1 /\ pre2 r1 s1 /\ post2 r1 (snd v) s1 r2 s2)

let fold_pair
  (#state_t: Type)
  #t1 #ret1 #pre1 #post1
  (f1: fold_t state_t t1 ret1 pre1 post1)
  #t2 #ret2 (#pre2: ret1 -> _) (#post2: ret1 -> _)
  (f2: (x: ret1) -> fold_t state_t t2 ret2 (pre2 x) (post2 x))
: Pure (fold_t state_t (t1 & t2) ret2 pre1 (fold_pair_post pre1 post1 pre2 post2))
    (requires (
      (forall s v1 r1 s' . post1 v1 s r1 s' ==> pre2 r1 s')
    ))
    (ensures (fun _ -> True))
= fun x s0 ->
    let x1 = fst x in
    let x2 = snd x in
    let (r1, s1) = f1 x1 s0 in
    f2 r1 x2 s1

let fold_list
  (#state_t: Type)
  (#inv: state_t -> prop)
  (#t: Type)
  (f: fold_t state_t t unit inv (fun _ _ _ -> inv))
: Tot (fold_t state_t (list t) unit inv (fun _ _ _ -> inv))
= fun l x -> ((), (List.Tot.fold_left (fun (state: state_t { inv state }) x -> snd (f x state)) x l <: state_t))

let fold_choice_post
  (#state_t: Type)
  (#ret_t: Type)
  (#t: bool -> Type)
  (post: (x: bool) -> t x -> state_t -> ret_t -> state_t -> prop)
  (v: (x: bool & t x))
  (s: state_t)
  (r: ret_t)
  (s': state_t)
: Tot prop
= post (dfst v) (dsnd v) s r s'

let fold_choice
  (#state_t: Type)
  (#ret_t: Type)
  (#t: bool -> Type)
  (#pre: state_t -> prop)
  (#post: (x: bool) -> t x -> state_t -> ret_t -> state_t -> prop)
  (f: (x: bool) -> fold_t state_t (t x) ret_t pre (post x))
: Tot (fold_t state_t (x: bool & t x) ret_t pre (fold_choice_post post))
= fun w -> if (dfst w) then f true (dsnd w) else f false (dsnd w)

let bind_fold_post
  (#state_t: Type)
  #t #ret1
  (pre1: state_t -> prop)
  (post1: t -> state_t -> ret1 -> state_t -> prop)
  #ret2
  (pre2: ret1 -> state_t -> prop)
  (post2: (x: ret1) -> t -> state_t -> ret2 -> state_t -> prop)
  (v: t)
  (s0: state_t)
  (r2: ret2)
  (s2: state_t)
: Tot prop
= pre1 s0 /\ (exists s1 r1 . post1 v s0 r1 s1 /\ pre2 r1 s1 /\ post2 r1 v s1 r2 s2)

let bind_fold
  (#state_t: Type)
  (#t: Type)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#pre2: _)
  (#post2: _)
  (f: fold_t state_t t ret1 pre1 post1)
  (g: (x: ret1) -> fold_t state_t t ret2 (pre2 x) (post2 x))
: Pure (fold_t state_t t ret2 pre1 (bind_fold_post pre1 post1 pre2 post2))
    (requires (forall s v r s' . post1 s v r s' ==> pre2 r s'))
    (ensures (fun _ -> True))
= fun v s0 ->
  let (r1, s1) = f v s0 in
  g r1 v s1

let ret_fold
  (#state_t: Type)
  (#ret_t: Type)
  (#pre #post: _)
  (#t: Type)
  (f: stt state_t ret_t pre post)
: Tot (fold_t state_t t ret_t pre (fun _ -> post))
= fun _ -> f

noeq
type action
  (state_t: Type)
  (action_impl_t: (t: Type) -> (pre: _) -> (post: _) -> stt state_t t pre post -> Type)
  (t: Type)
  (pre: _)
  (post: _)
= {
  action_spec: stt state_t t pre post;
  action_impl: action_impl_t _ _ _ action_spec;
}

noeq
type prog
  (state_t: Type)
  (action_impl_t: (t: Type) -> (pre: _) -> (post: _) -> stt state_t t pre post -> Type)
: (t: typ) -> (ret_t: Type) -> (state_t -> prop) -> (type_of_typ t -> state_t -> ret_t -> state_t -> prop) -> Type
= | PRet:
      (#t: typ) ->
      (#ret_t: Type) -> (#pre: _) -> (#post: _) ->
      action state_t action_impl_t ret_t pre post ->
      prog state_t action_impl_t t ret_t pre (fun _ -> post)
  | PBind:
      (#t: typ) ->
      (#ret1: Type) ->
      (#pre1: _) ->
      (#post1: _) ->
      (#ret2: _) ->
      (#pre2: _) ->
      (#post2: _) ->
      (f: prog state_t action_impl_t t ret1 pre1 post1) ->
      (g: ((x: ret1) -> prog state_t action_impl_t t ret2 (pre2 x) (post2 x)) {
        forall s v r s' . post1 s v r s' ==> pre2 r s'
      }) ->
      prog state_t action_impl_t t ret2 pre1 (bind_fold_post pre1 post1 pre2 post2)
  | PU8:
      (#ret_t: _) -> (#pre: _) -> (#post: _) ->
      ((x: U8.t) -> action state_t action_impl_t ret_t pre (post x)) ->
      prog state_t action_impl_t TU8 ret_t pre post
  | PPair:
      (#t1: _) ->
      (#ret1: _) ->
      (#pre1: _) ->
      (#post1: _) ->
      (f1: prog state_t action_impl_t t1 ret1 pre1 post1) ->
      (#t2: _) ->
      (#ret2: _) ->
      (#pre2: (ret1 -> _)) ->
      (#post2: (ret1 -> _)) ->
      (f2: ((x: ret1) -> prog state_t action_impl_t t2 ret2 (pre2 x) (post2 x)) {
        forall s v1 r1 s' . post1 v1 s r1 s' ==> pre2 r1 s'
      }) ->
      prog state_t action_impl_t (TPair t1 t2) ret2 pre1 (fold_pair_post pre1 post1 pre2 post2)
  | PList:
      (#t: typ) ->
      (#inv: _) ->
      prog state_t action_impl_t t unit inv (fun _ _ _ -> inv) ->
      prog state_t action_impl_t (TList t) unit inv (fun _ _ _ -> inv)
  | PChoice:
      (t: (bool -> typ)) -> // FIXME: WHY WHY WHY does this argument need to be explicit? (if not, then I get "this pattern binds to an inaccessible argument" in `sem` below)
      (#ret_t: Type) ->
      (#pre: (state_t -> prop)) ->
      (#post: ((x: bool) -> type_of_typ (t x) -> state_t -> ret_t -> state_t -> prop)) ->
      ((x: bool) -> prog state_t action_impl_t (t x) ret_t pre (post x)) ->
      prog state_t action_impl_t (TChoice t) ret_t pre (fold_choice_post post)

let rec sem
  (#state_t: Type)
  (#action_impl_t: (t: Type) -> (pre: _) -> (post: _) -> stt state_t t pre post -> Type)
  (#t: typ)
  (#ret_t: Type)
  (#pre: state_t -> prop)
  (#post: type_of_typ t -> state_t -> ret_t -> state_t -> prop)
  (p: prog state_t action_impl_t t ret_t pre post)
: Tot (fold_t state_t (type_of_typ t) ret_t pre post)
= match p returns (fold_t state_t (type_of_typ t) ret_t pre post) with
  | PRet s -> ret_fold s.action_spec
  | PBind s p -> bind_fold (sem s) (fun x -> sem (p x))
  | PU8 s -> (fun x -> (s x).action_spec)
  | PPair p1 p2 -> fold_pair (sem p1) (fun r -> sem (p2 r))
  | PList p -> fold_list (sem p)
  | PChoice f (* here, "inaccessible argument" *) p -> fold_choice (fun x -> sem (p x)) <: fold_t state_t (type_of_typ (TChoice f)) ret_t pre post

(* Step-by-step serialization *)

noeq
type base_context_t
  (erase_values: bool)
  : typ -> typ -> Type
= | CPairL: (l: typ) -> (r: typ) -> base_context_t erase_values (TPair l r) l
  | CPairR: (l: typ) -> (vl: (if erase_values then unit else type_of_typ l)) -> (r: typ) -> base_context_t erase_values (TPair l r) r
  | CListCons: (t: typ) -> (l: (if erase_values then unit else list (type_of_typ t))) -> base_context_t erase_values (TList t) t
  | CChoicePayload: (f: (bool -> typ)) -> (tag: bool) -> base_context_t erase_values (TChoice f) (f tag)

let base_context_erase_values
  (#erase_values: bool)
  (#t1: _)
  (#t2: _)
  (x: base_context_t erase_values t1 t2)
: Tot (base_context_t true t1 t2)
= match x with
  | CPairL l r -> CPairL l r
  | CPairR l _ r -> CPairR l () r
  | CListCons t _ -> CListCons t ()
  | CChoicePayload f tag -> CChoicePayload f tag

noeq
type context_t
  (erase_values: bool)
  : typ -> typ -> Type
= | CNil: (#t: typ) -> context_t erase_values t t
  | CSnoc: (#t1: typ) -> (#t2: typ) -> (#t3: typ) -> context_t erase_values t1 t2 -> base_context_t erase_values t2 t3 -> context_t erase_values t1 t3

let rec context_erase_values
  (#erase_values: bool)
  (#t1 #t2: _)
  (x: context_t erase_values t1 t2)
: Tot (context_t true t1 t2)
  (decreases x)
= match x with
  | CNil -> CNil
  | CSnoc c b -> CSnoc (context_erase_values c) (base_context_erase_values b)

let rec concat_context
  (#erase_values: bool)
  (#t1 #t2 #t4: typ)
  (c12: context_t erase_values t1 t2)
  (c24: context_t erase_values t2 t4)
: Tot (context_t erase_values t1 t4)
  (decreases c24)
= match c24 with
  | CNil -> c12
  | CSnoc c23 b34 -> CSnoc (concat_context c12 c23) b34

let rec erase_values_concat_context
  (#erase_values: bool)
  (#t1 #t2 #t4: typ)
  (c12: context_t erase_values t1 t2)
  (c24: context_t erase_values t2 t4)
: Lemma
  (requires True)
  (ensures (context_erase_values (c12 `concat_context` c24) == context_erase_values c12 `concat_context` context_erase_values c24))
  (decreases c24)
= match c24 with
  | CNil -> ()
  | CSnoc c23 b34 -> erase_values_concat_context c12 c23

noeq
type base_hole_t
  (erase_values: bool)
  : typ -> Type
= | HU8: base_hole_t erase_values TU8
  | HList: (t: typ) -> (l: (if erase_values then unit else list (type_of_typ t))) -> base_hole_t erase_values (TList t)
  | HChoiceTag: (f: (bool -> typ)) -> base_hole_t erase_values (TChoice f)

let base_hole_erase_values
  (#erase_values: bool)
  (#t: typ)
  (x: base_hole_t erase_values t)
: Tot (base_hole_t true t)
= match x with
  | HU8 -> HU8
  | HList t _ -> HList t ()
  | HChoiceTag f -> HChoiceTag f

noeq
type hole_t
  (erase_values: bool)
= {
  root: typ;
  leaf: typ;
  context: context_t erase_values root leaf;
  hole: base_hole_t erase_values leaf;
}

let hole_erase_values
  (#erase_values: bool)
  (x: hole_t erase_values)
: Tot (hole_t true)
= {
  root = x.root;
  leaf = x.leaf;
  context = context_erase_values x.context;
  hole = base_hole_erase_values x.hole;
}

let rec init_hole
  (erase_values: bool)
  (t: typ)
: Pure (hole_t erase_values)
  (requires True)
  (ensures (fun res -> res.root == t))
= match t with
  | TU8 -> { root = TU8; leaf = TU8; context = CNil; hole = HU8 }
  | TList t -> { root = TList t; leaf = TList t; context = CNil; hole = HList t (if erase_values then () else ([] <: list (type_of_typ t))) }
  | TChoice f -> { root = TChoice f; leaf = TChoice f; context = CNil; hole = HChoiceTag f }
  | TPair l r ->
    let h = init_hole erase_values l in
    { root = TPair l r; leaf = h.leaf; context = concat_context (CSnoc CNil (CPairL l r)) h.context; hole = h.hole }

let rec erase_values_init_hole
  (erase_values: bool)
  (t: typ)
: Lemma
  (hole_erase_values (init_hole erase_values t) == init_hole true t)
= match t with
  | TU8 -> ()
  | TList t -> ()
  | TChoice f -> ()
  | TPair l r ->
    erase_values_init_hole erase_values l;
    let h = init_hole erase_values l in
    erase_values_concat_context (CSnoc CNil (CPairL l r)) h.context

noeq
type hole_or_value_t
  (erase_values: bool)
  (t: typ)
= | Value: (if erase_values then unit else type_of_typ t) -> hole_or_value_t erase_values t
  | Hole: (h: hole_t erase_values { h.root == t }) -> hole_or_value_t erase_values t

let hole_or_value_erase_values
  (#erase_values: _)
  (#t: typ)
  (h: hole_or_value_t erase_values t)
: Tot (hole_or_value_t true t)
= match h with
  | Value _ -> Value ()
  | Hole h -> Hole (hole_erase_values h)

let mk_choice_value
  (tag: bool)
  (f: bool -> typ)
  (v: type_of_typ (f tag))
: Tot (type_of_typ (TChoice f))
= (| tag, v |)

let rec fill_context
  (#erase_values: bool)
  (#root: typ)
  (#leaf: typ)
  (c: context_t erase_values root leaf)
  (v: (if erase_values then unit else type_of_typ leaf))
: Tot (hole_or_value_t erase_values root)
  (decreases c)
= match c with
  | CNil ->
    Value v
  | CSnoc c' (CPairL l r) ->
    let h = init_hole erase_values r in
    Hole ({ root = root; leaf = h.leaf; context = concat_context (CSnoc c' (CPairR l v r)) h.context; hole = h.hole })
  | CSnoc c' (CPairR l vl r) ->
    fill_context c' (if erase_values then () else (vl, v))
  | CSnoc c' (CListCons t l) ->
    Hole ({ root = root; leaf = _; context = c'; hole = HList t (if erase_values then () else l `List.Tot.append` [v] )})
  | CSnoc c' (CChoicePayload f tag) ->
    fill_context c' (if erase_values then () else mk_choice_value tag f v)

let rec erase_values_fill_context
  (#erase_values: bool)
  (#root: typ)
  (#leaf: typ)
  (c: context_t erase_values root leaf)
  (v: (if erase_values then unit else type_of_typ leaf))
: Lemma
  (requires True)
  (ensures (hole_or_value_erase_values (fill_context c v) == fill_context (context_erase_values c) ()))
  (decreases c)
= match c with
  | CNil -> ()
  | CSnoc c' (CPairL l r) ->
    erase_values_init_hole erase_values r;
    let h = init_hole erase_values r in
    erase_values_concat_context (CSnoc c' (CPairR l v r)) h.context
  | CSnoc c' (CPairR l vl r) ->
    erase_values_fill_context c' (if erase_values then () else (vl, v))
  | CSnoc c' (CListCons t l) -> ()
  | CSnoc c' (CChoicePayload f tag) ->
    erase_values_fill_context c' (if erase_values then () else mk_choice_value tag f v)

let transition'_u8
  (#erase_values: bool)
  (h: hole_t erase_values { h.leaf == TU8 })
  (v: (if erase_values then unit else U8.t))
: Tot (hole_or_value_t erase_values h.root)
= fill_context h.context v

let transition_u8
  (t: typ)
  (v: U8.t)
: Tot (stt (hole_or_value_t false t) unit (fun s -> Hole? s /\ (Hole?.h s).leaf == TU8) (fun s _ s' ->
      Hole? s /\ (Hole?.h s).leaf == TU8 /\
      hole_or_value_erase_values s' == transition'_u8 (Hole?.h (hole_or_value_erase_values s)) ()
  ))
= fun s ->
  let Hole h = s in
  erase_values_fill_context h.context v;
  ((), transition'_u8 h v)

let transition'_list_nil
  (#erase_values: bool)
  (h: hole_t erase_values { TList? h.leaf })
: Tot (hole_or_value_t erase_values h.root)
= let TList t = h.leaf in
  fill_context h.context (if erase_values then () else ([] <: list (type_of_typ t)))

let transition_list_nil
  (t: typ)
: Tot (stt (hole_or_value_t false t) unit (fun s -> Hole? s /\ TList? (Hole?.h s).leaf) (fun s _ s' ->
    Hole? s /\ TList? (Hole?.h s).leaf /\
    hole_or_value_erase_values s' == transition'_list_nil (Hole?.h (hole_or_value_erase_values s))
  ))
= fun s ->
  let Hole h = s in
  let TList t' = h.leaf in
  erase_values_fill_context h.context ([] <: list (type_of_typ t'));
  ((), transition'_list_nil h)

let transition'_list_cons
  (#erase_values: bool)
  (h: hole_t erase_values { TList? h.leaf })
: Tot (hole_or_value_t erase_values h.root)
= let TList t = h.leaf in
  let HList _ l = h.hole in
  let h' = init_hole erase_values t in
  Hole ({
    root = h.root;
    leaf = h'.leaf;
    context = concat_context (CSnoc h.context (CListCons t l)) h'.context;
    hole = h'.hole;
  })

let transition_list_cons
  (t: typ)
: Tot (stt (hole_or_value_t false t) unit (fun s -> Hole? s /\ TList? (Hole?.h s).leaf) (fun s _ s' ->
    Hole? s /\ TList? (Hole?.h s).leaf /\
    hole_or_value_erase_values s' == transition'_list_cons (Hole?.h (hole_or_value_erase_values s))
  ))
= fun s ->
  let Hole h = s in
  let TList t' = h.leaf in
  let HList _ l = h.hole in
  erase_values_init_hole false t';
  let h' = init_hole false t' in
  erase_values_concat_context (CSnoc h.context (CListCons t' l)) h'.context;
  ((), transition'_list_cons h)

let transition'_choice_tag
  (#erase_values: bool)
  (h: hole_t erase_values { TChoice? h.leaf })
  (tag: bool)
: Tot (hole_or_value_t erase_values h.root)
= let TChoice f = h.leaf in
  let h' = init_hole erase_values (f tag) in
  Hole ({
    root = h.root;
    leaf = h'.leaf;
    context = concat_context (CSnoc h.context (CChoicePayload f tag)) h'.context;
    hole = h'.hole;
  })

let transition_choice_tag
  (t: typ)
  (tag: bool)
: Tot (stt (hole_or_value_t false t) unit (fun s -> Hole? s /\ TChoice? (Hole?.h s).leaf) (fun s _ s' ->
    Hole? s /\ TChoice? (Hole?.h s).leaf /\
    hole_or_value_erase_values s' == transition'_choice_tag (Hole?.h (hole_or_value_erase_values s)) tag
  ))
= fun s ->
  let Hole h = s in
  let TChoice f = h.leaf in
  erase_values_init_hole false (f tag);
  let h' = init_hole false (f tag) in
  erase_values_concat_context (CSnoc h.context (CChoicePayload f tag)) h'.context;
  ((), transition'_choice_tag h tag)

let mk_unit_action
  (#state_t: Type)
  (#t: Type)
  (#pre: _)
  (#post: _)
  (f: stt state_t t pre post)
: Tot (action state_t (fun _ _ _ _ -> unit) t pre post)
= {
  action_spec = f;
  action_impl = ();
}

let _ : prog (hole_or_value_t false (TPair TU8 TU8)) (fun _ _ _ _ -> unit) (TPair TU8 TU8) unit _ _ =
  PPair
    (PBind
      (PRet (mk_unit_action (state_assert (fun s -> s == Hole (init_hole false (TPair TU8 TU8))))))
      (fun _ -> PU8 (fun x1 -> mk_unit_action (transition_u8 _ x1))))
    (fun _ -> PU8 (fun x2 -> mk_unit_action (transition_u8 _ x2)))

let _ : prog (hole_or_value_t false (TPair TU8 TU8)) (fun _ _ _ _ -> unit) (TPair TU8 TU8) unit _ _ =
  PBind
    (PPair
      (PRet (mk_unit_action (state_assert (fun s -> s == Hole (init_hole false (TPair TU8 TU8))))))
      (fun _ -> PU8 (fun x2 -> mk_unit_action (transition_u8 _ x2))))
    (fun _ -> PPair
       (PU8 (fun x1 -> mk_unit_action (transition_u8 _ x1)))
       (fun _ -> PRet (mk_unit_action (ret ()))))
