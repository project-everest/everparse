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

let fold_t (state_t: Type) (pre post: state_t -> prop) (t: Type) : Tot Type = (t -> stt state_t unit pre (fun _ _ -> post))

let fold_pair
  (#state_t: Type)
  (#pre1 #post1 #pre2 #post2: state_t -> prop)
  (#t1 #t2: Type)
  (f1: fold_t state_t pre1 post1 t1)
  (f2: fold_t state_t pre2 post2 t2)
: Pure (fold_t state_t pre1 post2 (t1 & t2))
    (requires (forall s . post1 s ==> pre2 s))
    (ensures (fun _ -> True))
= fun (x1, x2) -> bind (f1 x1) (fun _ -> f2 x2)

let fold_list
  (#state_t: Type)
  (#inv: state_t -> prop)
  (#t: Type)
  (f: fold_t state_t inv inv t)
: Tot (fold_t state_t inv inv (list t))
= fun l x -> ((), (List.Tot.fold_left (fun (state: state_t { inv state }) x -> snd (f x state)) x l <: state_t))

let fold_choice
  (#state_t: Type)
  (#pre #post: state_t -> prop)
  (#t: bool -> Type)
  (f: (x: bool) -> fold_t state_t pre post (t x))
: Tot (fold_t state_t pre post (x: bool & t x))
= fun w -> if (dfst w) then f true (dsnd w) else f false (dsnd w)

let bind_fold
  (#state_t: Type)
  (#ret_t: Type)
  (#pre1: _)
  (#post1: _)
  (#pre2 #post2: _)
  (#t: Type)
  (f: stt state_t ret_t pre1 post1)
  (g: ret_t -> fold_t state_t pre2 post2 t)
: Pure (fold_t state_t pre1 post2 t)
    (requires (forall s r s' . post1 s r s' ==> pre2 s'))
    (ensures (fun _ -> True))
= fun x -> bind f (fun r -> g r x)

let seq_fold
  (#state_t: Type)
  (#pre1 #post1 #pre2 #post2: _)
  (#t: Type)
  (f1: fold_t state_t pre1 post1 t)
  (f2: fold_t state_t pre2 post2 t)
: Pure (fold_t state_t pre1 post2 t)
    (requires (forall s . post1 s ==> pre2 s))
    (ensures (fun _ -> True))
= fun x -> bind (f1 x) (fun _ -> f2 x)

let ret_fold
  (#state_t: Type)
  (#pre #post: _)
  (#t: Type)
  (f: stt state_t unit pre (fun _ _ -> post))
: Tot (fold_t state_t pre post t)
= fun _ -> f

noeq
type prog
  (state_t: Type)
  (action_t: (t: Type) -> (pre: _) -> (post: _) -> stt state_t t pre post -> Type)
: (state_t -> prop) -> (state_t -> prop) -> typ -> Type
= | PRet: (#pre: _) -> (#post: _) -> (t: typ) -> (s: stt state_t unit pre (fun _ _ -> post)) -> action_t _ pre (fun _ _ -> post) s -> prog state_t action_t pre post t
  | PSeq: (#t: typ) -> (#pre1: _) -> (#post1: (_ -> prop)) -> (#pre2: (_ -> prop)  { forall s . post1 s ==> pre2 s }) -> (#post2: _) -> prog state_t action_t pre1 post1 t -> prog state_t action_t pre2 post2 t -> prog state_t action_t pre1 post2 t
  | PBind: (#r: Type) -> (#pre1: _) -> (#post1: (_ -> _ -> _ -> prop)) -> (#pre2: (_ -> prop) { forall s0 r1 s1 . post1 s0 r1 s1 ==> pre2 s1 }) -> (#post2: _) -> (#t: typ) -> (s: stt state_t r pre1 post1) -> action_t r pre1 post1 s -> (r -> prog state_t action_t pre2 post2 t) -> prog state_t action_t pre1 post2 t
  | PU8: (#pre: _) -> (#post: _) -> (s: (U8.t -> stt state_t unit pre (fun _ _ -> post))) -> ((x: U8.t) -> action_t _ _ _ (s x)) -> prog state_t action_t pre post TU8
  | PPair: (#t1: typ) -> (#t2: typ) -> (#pre1: _) -> (#post1: (_ -> prop)) -> (#pre2: (_ -> prop) { forall s . post1 s ==> pre2 s }) -> (#post2: _) -> prog state_t action_t pre1 post1 t1 -> prog state_t action_t pre2 post2 t2 -> prog state_t action_t pre1 post2 (TPair t1 t2)
  | PList: (#t: typ) -> (#inv: _) -> prog state_t action_t inv inv t -> prog state_t action_t inv inv (TList t)
  | PChoice: (f: (bool -> typ)) -> (#pre: _) -> (#post: _) -> ((x: bool) -> prog state_t action_t pre post (f x)) -> prog state_t action_t pre post (TChoice f)

let rec sem
  (#state_t: Type)
  (#action_t: (t: Type) -> (pre: _) -> (post: _) -> stt state_t t pre post -> Type)
  (#pre: _)
  (#post: _)
  (#t: typ)
  (p: prog state_t action_t pre post t)
: Tot (fold_t state_t pre post (type_of_typ t))
= match p returns fold_t state_t pre post (type_of_typ t) with
  | PRet _ s _ -> ret_fold s
  | PSeq p1 p2 -> seq_fold (sem p1) (sem p2)
  | PBind s _ p -> bind_fold s (fun x -> sem (p x))
  | PU8 s _ -> s
  | PPair p1 p2 -> fold_pair (sem p1) (sem p2)
  | PList p -> fold_list (sem p)
  | PChoice f p -> fold_choice (fun x -> sem (p x)) <: fold_t state_t pre post (type_of_typ (TChoice f))

(* Step-by-step serialization *)

noeq
type base_context_t
  : typ -> typ -> Type
= | CPairL: (l: typ) -> (r: typ) -> base_context_t (TPair l r) l
  | CPairR: (l: typ) -> (vl: type_of_typ l) -> (r: typ) -> base_context_t (TPair l r) r
  | CListCons: (t: typ) -> (l: list (type_of_typ t)) -> base_context_t (TList t) t
  | CChoicePayload: (f: (bool -> typ)) -> (tag: bool) -> base_context_t (TChoice f) (f tag)

noeq
type context_t
  : typ -> typ -> Type
= | CNil: (#t: typ) -> context_t t t
  | CSnoc: (#t1: typ) -> (#t2: typ) -> (#t3: typ) -> context_t t1 t2 -> base_context_t t2 t3 -> context_t t1 t3

let rec concat_context
  (#t1 #t2 #t4: typ)
  (c12: context_t t1 t2)
  (c24: context_t t2 t4)
: Tot (context_t t1 t4)
  (decreases c24)
= match c24 with
  | CNil -> c12
  | CSnoc c23 b34 -> CSnoc (concat_context c12 c23) b34

noeq
type base_hole_t
  : typ -> Type
= | HU8: base_hole_t TU8
  | HList: (t: typ) -> (l: list (type_of_typ t)) -> base_hole_t (TList t)
  | HChoiceTag: (f: (bool -> typ)) -> base_hole_t (TChoice f)

noeq
type hole_t
= {
  root: typ;
  leaf: typ;
  context: context_t root leaf;
  hole: base_hole_t leaf;
}

let rec init_hole
  (t: typ)
: Pure hole_t
  (requires True)
  (ensures (fun res -> res.root == t))
= match t with
  | TU8 -> { root = TU8; leaf = TU8; context = CNil; hole = HU8 }
  | TList t -> { root = TList t; leaf = TList t; context = CNil; hole = HList t [] }
  | TChoice f -> { root = TChoice f; leaf = TChoice f; context = CNil; hole = HChoiceTag f }
  | TPair l r ->
    let h = init_hole l in
    { root = TPair l r; leaf = h.leaf; context = concat_context (CSnoc CNil (CPairL l r)) h.context; hole = h.hole }

noeq
type hole_or_value_t
  (t: typ)
= | Value: type_of_typ t -> hole_or_value_t t
  | Hole: (h: hole_t { h.root == t }) -> hole_or_value_t t

let mk_choice_value
  (tag: bool)
  (f: bool -> typ)
  (v: type_of_typ (f tag))
: Tot (type_of_typ (TChoice f))
= (| tag, v |)

let rec fill_context
  (#root: typ)
  (#leaf: typ)
  (c: context_t root leaf)
  (v: type_of_typ leaf)
: Tot (hole_or_value_t root)
  (decreases c)
= match c with
  | CNil ->
    Value v
  | CSnoc c' (CPairL l r) ->
    let h = init_hole r in
    Hole ({ root = root; leaf = h.leaf; context = concat_context (CSnoc c' (CPairR l v r)) h.context; hole = h.hole })
  | CSnoc c' (CPairR l vl r) ->
    fill_context c' (vl, v)
  | CSnoc c' (CListCons t l) ->
    Hole ({ root = root; leaf = _; context = c'; hole = HList t (l `List.Tot.append` [v] )})
  | CSnoc c' (CChoicePayload f tag) ->
    fill_context c' (mk_choice_value tag f v)

let transition'_u8
  (v: U8.t)
  (h: hole_t { h.leaf == TU8 })
: Tot (hole_or_value_t h.root)
= fill_context h.context v

let transition_u8
  (t: typ)
  (v: U8.t)
: Tot (stt (hole_or_value_t t) unit (fun s -> Hole? s /\ (Hole?.h s).leaf == TU8) (fun _ _ _ -> True))
= fun s ->
  let Hole h = s in
  ((), transition'_u8 v h)

let transition'_list_nil
  (h: hole_t { TList? h.leaf })
: Tot (hole_or_value_t h.root)
= let TList t = h.leaf in
  fill_context h.context ([] <: list (type_of_typ t))

let transition_list_nil
  (t: typ)
: Tot (stt (hole_or_value_t t) unit (fun s -> Hole? s /\ TList? (Hole?.h s).leaf) (fun _ _ _ -> True))
= fun s ->
  let Hole h = s in
  ((), transition'_list_nil h)

let transition'_list_cons
  (h: hole_t { TList? h.leaf })
: Tot (hole_or_value_t h.root)
= let TList t = h.leaf in
  let HList _ l = h.hole in
  let h' = init_hole t in
  Hole ({
    root = h.root;
    leaf = h'.leaf;
    context = concat_context (CSnoc h.context (CListCons t l)) h'.context;
    hole = h'.hole;
  })

let transition_list_cons
  (t: typ)
: Tot (stt (hole_or_value_t t) unit (fun s -> Hole? s /\ TList? (Hole?.h s).leaf) (fun _ _ _ -> True))
= fun s ->
  let Hole h = s in
  ((), transition'_list_cons h)

let transition'_choice_tag
  (h: hole_t { TChoice? h.leaf })
  (tag: bool)
: Tot (hole_or_value_t h.root)
= let TChoice f = h.leaf in
  let h' = init_hole (f tag) in
  Hole ({
    root = h.root;
    leaf = h'.leaf;
    context = concat_context (CSnoc h.context (CChoicePayload f tag)) h'.context;
    hole = h'.hole;
  })

let transition_choice_tag
  (t: typ)
  (tag: bool)
: Tot (stt (hole_or_value_t t) unit (fun s -> Hole? s /\ TChoice? (Hole?.h s).leaf) (fun _ _ _ -> True))
= fun s ->
  let Hole h = s in
  ((), transition'_choice_tag h tag)
