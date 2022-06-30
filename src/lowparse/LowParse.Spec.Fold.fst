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
type prog
  (state_t: Type)
  (action_t: (ret_t: Type) -> (pre: state_t -> prop) -> (post: state_t -> ret_t -> state_t -> prop) -> Type)
: (t: typ) -> (ret_t: Type) -> (state_t -> prop) -> (type_of_typ t -> state_t -> ret_t -> state_t -> prop) -> Type
= | PSubcomp:
      (#t: typ) ->
      (#ret_t: Type) ->
      (pre_out: (state_t -> prop)) ->
      (#pre_in: (state_t -> prop) {
        forall s . pre_out s ==> pre_in s
      }) ->
      (#post_in: (type_of_typ t -> state_t -> ret_t -> state_t -> prop)) ->
      prog state_t action_t t ret_t pre_in post_in ->
      (post_out: (type_of_typ t -> state_t -> ret_t -> state_t -> prop) {
        forall v s r s' . post_in v s r s' ==> post_out v s r s'
      }) ->
      prog state_t action_t t ret_t pre_out post_out
  | PRet:
      (#t: typ) ->
      (#ret_t: Type) ->
      (v: ret_t) ->
      prog state_t action_t t ret_t (fun _ -> True) (fun _ s res s' -> s' == s /\ res == v)
  | PAction:
      (#t: typ) ->
      (#ret_t: Type) -> (#pre: _) -> (#post: _) ->
      action_t ret_t pre post ->
      prog state_t action_t t ret_t pre (fun _ -> post)
  | PBind:
      (#t: typ) ->
      (#ret1: Type) ->
      (#pre1: _) ->
      (#post1: _) ->
      (#ret2: _) ->
      (#pre2: _) ->
      (#post2: _) ->
      (f: prog state_t action_t t ret1 pre1 post1) ->
      (g: ((x: ret1) -> prog state_t action_t t ret2 (pre2 x) (post2 x)) {
        forall s v r s' . post1 s v r s' ==> pre2 r s'
      }) ->
      prog state_t action_t t ret2 pre1 (bind_fold_post pre1 post1 pre2 post2)
  | PU8:
      // the base action on a leaf type just reads the value;
      // use PBind with PAction and others to perform operations on that value
      prog state_t action_t TU8 U8.t (fun _ -> True) (fun x s res s' -> s == s' /\ res == x)
  | PPair:
      (#t1: _) ->
      (#ret1: _) ->
      (#pre1: _) ->
      (#post1: _) ->
      (f1: prog state_t action_t t1 ret1 pre1 post1) ->
      (#t2: _) ->
      (#ret2: _) ->
      (#pre2: (ret1 -> _)) ->
      (#post2: (ret1 -> _)) ->
      (f2: ((x: ret1) -> prog state_t action_t t2 ret2 (pre2 x) (post2 x)) {
        forall s v1 r1 s' . post1 v1 s r1 s' ==> pre2 r1 s'
      }) ->
      prog state_t action_t (TPair t1 t2) ret2 pre1 (fold_pair_post pre1 post1 pre2 post2)
  | PList:
      (#t: typ) ->
      (#inv: _) ->
      prog state_t action_t t unit inv (fun _ _ _ -> inv) ->
      prog state_t action_t (TList t) unit inv (fun _ _ _ -> inv)
  | PChoice:
      (t: (bool -> typ)) -> // FIXME: WHY WHY WHY does this argument need to be explicit? (if not, then I get "this pattern binds to an inaccessible argument" in `sem` below)
      (#ret_t: Type) ->
      (#pre: (state_t -> prop)) ->
      (#post: ((x: bool) -> type_of_typ (t x) -> state_t -> ret_t -> state_t -> prop)) ->
      ((x: bool) -> prog state_t action_t (t x) ret_t pre (post x)) ->
      prog state_t action_t (TChoice t) ret_t pre (fold_choice_post post)

let rec sem
  (#state_t: Type)
  (#action_t: (t: Type) -> (pre: _) -> (post: _) -> Type)
  (action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
  (#t: typ)
  (#ret_t: Type)
  (#pre: state_t -> prop)
  (#post: type_of_typ t -> state_t -> ret_t -> state_t -> prop)
  (p: prog state_t action_t t ret_t pre post)
: Tot (fold_t state_t (type_of_typ t) ret_t pre post)
= match p returns (fold_t state_t (type_of_typ t) ret_t pre post) with
  | PSubcomp _ p _ -> (fun v -> sem action_sem p v)
  | PRet v -> ret_fold (ret v)
  | PAction a -> ret_fold (action_sem a)
  | PBind s p -> bind_fold (sem action_sem s) (fun x -> sem action_sem (p x))
  | PU8 -> (fun x -> ret x)
  | PPair p1 p2 -> fold_pair (sem action_sem p1) (fun r -> sem action_sem (p2 r))
  | PList p -> fold_list (sem action_sem p)
  | PChoice f (* here, "inaccessible argument" *) p -> fold_choice (fun x -> sem action_sem (p x)) <: fold_t state_t (type_of_typ (TChoice f)) ret_t pre post

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

noeq
type hole_or_value_t
  (erase_values: bool)
  (t: typ)
= | HVHole
  | HVValue: (if erase_values then unit else type_of_typ t) -> hole_or_value_t erase_values t

let hole_or_value_erase_values
  (#erase_values: _)
  (#t: _)
  (h: hole_or_value_t erase_values t)
: Tot (hole_or_value_t true t)
= match h with
  | HVHole -> HVHole
  | HVValue _ -> HVValue ()

noeq
type hole_t
  (erase_values: bool)
= {
  root: typ;
  leaf: typ;
  context: context_t erase_values root leaf;
  hole: hole_or_value_t erase_values leaf;
}

let hole_erase_values
  (#erase_values: bool)
  (x: hole_t erase_values)
: Tot (hole_t true)
= {
  root = x.root;
  leaf = x.leaf;
  context = context_erase_values x.context;
  hole = hole_or_value_erase_values x.hole;
}

let mk_choice_value
  (tag: bool)
  (f: bool -> typ)
  (v: type_of_typ (f tag))
: Tot (type_of_typ (TChoice f))
= (| tag, v |)

let close_hole
  (#erase_values: bool)
  (x: hole_t erase_values)
: Pure (hole_t erase_values)
  (requires (
    CSnoc? x.context /\
    HVValue? x.hole
  ))
  (ensures (fun _ -> True))
= let CSnoc c' c = x.context in
  let HVValue v = x.hole in
  match c with
  | CPairL l r ->
    {
      root = x.root;
      leaf = r;
      context = CSnoc c' (CPairR l v r);
      hole = HVHole;
    }
  | CPairR l vl r ->
    {
      root = x.root;
      leaf = _;
      context = c';
      hole = HVValue (if erase_values then () else (vl, v));
    }
  | CListCons t l ->
    {
      root = x.root;
      leaf = _;
      context = c';
      hole = HVValue (if erase_values then () else List.Tot.append l [v]);
    }
  | CChoicePayload f tag ->
    {
      root = x.root;
      leaf = _;
      context = c';
      hole = HVValue (if erase_values then () else mk_choice_value tag f v)
    }

let fill_hole
  (#erase_values: bool)
  (x: hole_t erase_values)
  (v: (if erase_values then unit else type_of_typ x.leaf))
: Pure (hole_t erase_values)
  (requires (HVHole? x.hole))
  (ensures (fun _ -> True))
= {
    x with
    hole = HVValue v;
  }

let start_pair
  (#erase_values: bool)
  (x: hole_t erase_values)
: Pure (hole_t erase_values)
  (requires (
    HVHole? x.hole /\
    TPair? x.leaf
  ))
  (ensures (fun _ -> True))
= let TPair l r = x.leaf in
  {
    root = x.root;
    leaf = l;
    context = CSnoc x.context (CPairL l r);
    hole = HVHole;
  }

let start_list
  (#erase_values: bool)
  (x: hole_t erase_values)
: Pure (hole_t erase_values)
  (requires (
    HVHole? x.hole /\
    TList? x.leaf
  ))
  (ensures (fun _ -> True))
= let TList t = x.leaf in
  fill_hole x (if erase_values then () else ([] <: list (type_of_typ t)))

let list_snoc
  (#erase_values: bool)
  (x: hole_t erase_values)
: Pure (hole_t erase_values)
  (requires (
    HVValue? x.hole /\
    TList? x.leaf
  ))
  (ensures (fun _ -> True))
= let TList t = x.leaf in
  let HVValue l = x.hole in
  {
    root = x.root;
    leaf = t;
    context = CSnoc x.context (CListCons t l);
    hole = HVHole;
  }

let choice_tag
  (#erase_values: bool)
  (x: hole_t erase_values)
  (tag: bool)
: Pure (hole_t erase_values)
  (requires (
    HVHole? x.hole /\
    TChoice? x.leaf
  ))
  (ensures (fun _ -> True))
= let TChoice f = x.leaf in
  {
    root = x.root;
    leaf = f tag;
    context = CSnoc x.context (CChoicePayload f tag);
    hole = HVHole;
  }

let ser_state = hole_t false
