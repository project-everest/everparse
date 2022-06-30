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

let stt (#state_i: Type) (state_t: (state_i -> Type)) (ret_t: Type) (pre: state_i) (post: (ret_t -> state_i)) : Tot Type = (state_t pre -> Tot (y: ret_t & state_t (post y)))

let ret_post #state_i (#ret_t: Type) (i: state_i) (x: ret_t) : Tot state_i = i

let ret #state_t #pre (#ret_t: Type) (x: ret_t) : Tot (stt state_t ret_t pre (ret_post pre)) = fun s -> (| x, s |)

let bind #state_i #state_t (#ret1_t #ret2_t: Type)
  (#pre1: state_i)
  (#post1: ret1_t -> state_i)
  (f1: stt state_t ret1_t pre1 post1)
  (#post2: ret2_t -> state_i)
  (f2: (r1: ret1_t) -> stt state_t ret2_t (post1 r1) post2)
: Tot (stt state_t ret2_t pre1 post2)
= fun state0 ->
    let (| r1, state1 |) = f1 state0 in
    let (| r2, state2 |) = f2 r1 state1 in
    (| r2, state2 |)

let fold_t #state_i (state_t: (state_i -> Type)) (t: Type) (ret_t: Type) (pre: state_i) (post: ret_t -> state_i) : Tot Type = ((v: t) -> stt state_t ret_t pre post)

let fold_pair
  #state_t
  #t1 #ret1 #pre1 #post1
  (f1: fold_t state_t t1 ret1 pre1 post1)
  #t2 #ret2 (#post2: _)
  (f2: (x: ret1) -> fold_t state_t t2 ret2 (post1 x) post2)
: Tot (fold_t state_t (t1 & t2) ret2 pre1 post2)
= fun x s0 ->
    let x1 = fst x in
    let x2 = snd x in
    let (| r1, s1 |) = f1 x1 s0 in
    f2 r1 x2 s1

let fold_list
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (ret_post inv))
: Tot (fold_t state_t (list t) unit inv (ret_post inv))
= fun l x -> (| (), (List.Tot.fold_left (fun (state: state_t inv) x -> dsnd (f x state)) x l <: state_t inv) |)

let fold_choice
  #state_i #state_t
  (#ret_t: Type)
  (#t: bool -> Type)
  (#pre: state_i)
  (#post: ret_t -> state_i)
  (f: (x: bool) -> fold_t state_t (t x) ret_t pre post)
: Tot (fold_t state_t (x: bool & t x) ret_t pre post)
= fun w -> if (dfst w) then f true (dsnd w) else f false (dsnd w)

let bind_fold
  #state_t
  (#t: Type)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#post2: _)
  (f: fold_t state_t t ret1 pre1 post1)
  (g: (x: ret1) -> fold_t state_t t ret2 (post1 x) post2)
: Tot (fold_t state_t t ret2 pre1 post2)
= fun v s0 ->
  let (| r1, s1 |) = f v s0 in
  g r1 v s1

let action_fold
  #state_t
  (#ret_t: Type)
  (#pre: _)
  (#post: _)
  (#t: Type)
  (f: stt state_t ret_t pre post)
: Tot (fold_t state_t t ret_t pre post)
= fun _ -> f

let fold_read
  #state_t
  (#pre: _)
  (#t: Type)
  ()
: Tot (fold_t state_t t t pre (ret_post pre))
= fun x -> ret x

noeq
type prog
  (#state_i: Type)
  (state_t: state_i -> Type)
  (action_t: (ret_t: Type) -> (pre: state_i) -> (post: ret_t -> state_i) -> Type)
: (t: typ) -> (ret_t: Type) -> state_i -> (ret_t -> state_i) -> Type
= | PRet:
      (#ret_t: Type) ->
      (#i: state_i) ->
      (#t: typ) ->
      (v: ret_t) ->
      prog state_t action_t t ret_t i (ret_post i)
  | PAction:
      (#t: typ) ->
      (#ret_t: Type) -> (#pre: _) -> (#post: _) ->
      action_t ret_t pre post ->
      prog state_t action_t t ret_t pre post
  | PBind:
      (#t: typ) ->
      (#ret1: Type) ->
      (#pre1: _) ->
      (#post1: _) ->
      (#ret2: _) ->
      (#post2: _) ->
      (f: prog state_t action_t t ret1 pre1 post1) ->
      (g: ((x: ret1) -> prog state_t action_t t ret2 (post1 x) post2)) ->
      prog state_t action_t t ret2 pre1 post2
  | PU8:
      // the base action on a leaf type just reads the value;
      // use PBind with PAction and others to perform operations on that value
      (i: state_i) ->
      prog state_t action_t TU8 U8.t i (ret_post i)
  | PPair:
      (#t1: _) ->
      (#ret1: _) ->
      (#pre1: _) ->
      (#post1: _) ->
      (f1: prog state_t action_t t1 ret1 pre1 post1) ->
      (#t2: _) ->
      (#ret2: _) ->
      (#post2: _) ->
      (f2: ((x: ret1) -> prog state_t action_t t2 ret2 (post1 x) post2)) ->
      prog state_t action_t (TPair t1 t2) ret2 pre1 post2
  | PList:
      (#t: typ) ->
      (inv: _) ->
      prog state_t action_t t unit inv (ret_post inv) ->
      prog state_t action_t (TList t) unit inv (ret_post inv)
  | PChoice:
      (#t: (bool -> typ)) ->
      (#ret_t: Type) ->
      (#pre: _) ->
      (#post: _) ->
      ((x: bool) -> prog state_t action_t (t x) ret_t pre post) ->
      prog state_t action_t (TChoice t) ret_t pre post

let rec sem
  #state_t
  (#action_t: (t: Type) -> (pre: _) -> (post: _) -> Type)
  (action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
  (#t: typ)
  (#ret_t: Type)
  (#pre: _)
  (#post: _)
  (p: prog state_t action_t t ret_t pre post)
: Tot (fold_t state_t (type_of_typ t) ret_t pre post)
  (decreases p)
= match p returns (fold_t state_t (type_of_typ t) ret_t pre post) with
  | PRet v -> action_fold (ret v) <: fold_t state_t (type_of_typ t) ret_t _ (ret_post _)
  | PAction a -> action_fold (action_sem a)
  | PBind s p -> bind_fold (sem action_sem s) (fun x -> sem action_sem (p x))
  | PU8 _ -> fold_read () <: fold_t state_t (type_of_typ t) ret_t _ (ret_post _)
  | PPair p1 p2 -> fold_pair (sem action_sem p1) (fun r -> sem action_sem (p2 r))
  | PList inv p -> fold_list inv (sem action_sem p)
  | PChoice p -> fold_choice (fun x -> sem action_sem (p x)) <: fold_t state_t (type_of_typ (TChoice _)) ret_t pre post

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

let ser_index : Type0 = hole_t true

let ser_state (i: ser_index) : Tot Type0 = (x: hole_t false {
  hole_erase_values x == i
})

let ser_close_hole
  (x: ser_index)
  (sq: squash (
    CSnoc? x.context /\
    HVValue? x.hole
  ))
: Tot (stt ser_state unit x (ret_post (close_hole x)))
= fun h -> (| (), close_hole h |)

let ser_u8
  (x: ser_index)
  (v: U8.t {
    x.leaf == TU8 /\
    HVHole? x.hole
  })
: Tot (stt ser_state unit x (ret_post (fill_hole x ())))
= fun h -> (| (), fill_hole h v |)

let ser_start_pair
  (x: ser_index)
  (sq: squash (
    TPair? x.leaf /\
    HVHole? x.hole
  ))
: Tot (stt ser_state unit x (ret_post (start_pair x)))
= fun h -> (| (), start_pair h |)

noeq
type ser_action
: (ret_t: Type) -> ser_index -> (ret_t -> ser_index) -> Type
= | SCloseHole:
      (#x: ser_index) ->
      squash (CSnoc? x.context /\ HVValue? x.hole) ->
      ser_action unit x (ret_post (close_hole x))
  | SU8:
      (#x: ser_index) ->
      (v: U8.t {
        x.leaf == TU8 /\
        HVHole? x.hole
      }) ->
      ser_action unit x (ret_post (fill_hole x ()))
  | SStartPair:
      (#x: ser_index) ->
      squash (TPair? x.leaf /\ HVHole? x.hole) ->
      ser_action unit x (ret_post (start_pair x))

let ser_action_sem
  (#ret_t: Type)
  (#pre: ser_index)
  (#post: (ret_t -> ser_index))
  (a: ser_action ret_t pre post)
: Tot (stt ser_state ret_t pre post)
= match a with
  | SCloseHole #x _ -> ser_close_hole x ()
  | SU8 #x v -> ser_u8 x v
  | SStartPair #x _ -> ser_start_pair x ()

(*
let test0 : prog _ ser_action _ _ (Mkhole_t (TPair TU8 TU8) _ CNil HVHole) _ =
  PBind
    (PAction (SStartPair ()))
    (fun _ ->
       PPair
         (PBind
            (PU8 _)
            (fun v ->
              PBind
                (PAction (SU8 v))
                (fun _ -> PAction (SCloseHole ()))
            )
         )
         (fun _ ->
          PBind
            (PU8 _)
            (fun v ->
              PBind
                (PAction (SU8 v))
                (fun _ -> PAction (SCloseHole ()))
            )
         )
    )
