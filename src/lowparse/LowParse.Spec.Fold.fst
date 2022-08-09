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

let stt (#state_i: Type) (state_t: (state_i -> Type)) (ret_t: Type) (pre: state_i) (post: (state_i)) : Tot Type = (state_t pre -> Tot (ret_t & state_t (post)))

let ret #state_t #pre (#ret_t: Type) (x: ret_t) : Tot (stt state_t ret_t pre (pre)) = fun s -> (x, s)

let bind #state_i #state_t (#ret1_t #ret2_t: Type)
  (#pre1: state_i)
  (#post1: state_i)
  (f1: stt state_t ret1_t pre1 post1)
  (#post2: state_i)
  (f2: (r1: ret1_t) -> stt state_t ret2_t (post1) post2)
: Tot (stt state_t ret2_t pre1 post2)
= fun state0 ->
    let (r1, state1) = f1 state0 in
    let (r2, state2) = f2 r1 state1 in
    (r2, state2)

let fold_t #state_i (state_t: (state_i -> Type)) (t: Type) (ret_t: Type) (pre: state_i) (post: state_i) : Tot Type = ((v: t) -> stt state_t ret_t pre post)

let fold_pair
  #state_t
  #t1 #ret1 #pre1 #post1
  (f1: fold_t state_t t1 ret1 pre1 post1)
  #t2 #ret2 (#post2: _)
  (f2: (x: ret1) -> fold_t state_t t2 ret2 (post1) post2)
: Tot (fold_t state_t (t1 & t2) ret2 pre1 post2)
= fun x s0 ->
    let x1 = fst x in
    let x2 = snd x in
    let (r1, s1) = f1 x1 s0 in
    f2 r1 x2 s1

let fold_list_f
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (inv))
  (state: state_t inv)
  (x: t)
: Tot (state_t inv)
= snd (f x state)

let fold_list
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (inv))
: Tot (fold_t state_t (list t) unit inv (inv))
= fun l x -> ((), List.Tot.fold_left (fold_list_f inv f) x l)

let fold_choice
  #state_i #state_t
  (#ret_t: Type)
  (#t: bool -> Type)
  (#pre: state_i)
  (#post: _)
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
  (g: (x: ret1) -> fold_t state_t t ret2 (post1) post2)
: Tot (fold_t state_t t ret2 pre1 post2)
= fun v s0 ->
  let (r1, s1) = f v s0 in
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

let rec fold_for
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (from: nat) (to: int)
  (f: (x: nat { from <= x /\ x <= to }) -> fold_t state_t t unit inv inv)
: Tot (fold_t state_t t unit inv inv)
  (decreases (if to < from then 0 else to - from + 1))
= if from > to
  then action_fold (ret ())
  else bind_fold (f from) (fun _ -> fold_for inv (from + 1) to f)

let fold_list_index
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (idx: (n: nat) -> Tot (i: nat { i < n }))
  (f: fold_t state_t t unit inv inv)
: Tot (fold_t state_t (list t) unit inv inv)
= fun l -> f (List.Tot.index l (idx (List.Tot.length l)))

let fold_list_index'
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (n: nat)
  (idx: (i: nat { i < n }))
  (f: fold_t state_t t unit inv inv)
: Tot (fold_t state_t (l: list t { List.Tot.length l == n }) unit inv inv)
= fun l -> f (List.Tot.index l idx)

let fold_for_list'
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (n: nat)
  (idx: (i: nat { i < n }) -> Tot (i: nat { i < n }))
: Tot (fold_t state_t (l: list t { List.Tot.length l == n }) unit inv inv)
= fold_for inv 0 (n - 1) (fun j -> fold_list_index' inv n (idx j) f)

let fold_for_list
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (idx: (n: nat) -> (i: nat { i < n }) -> Tot (i: nat { i < n }))
: Tot (fold_t state_t (list t) unit inv inv)
= fun l ->
  let n = List.Tot.length l in
  fold_for_list' inv f n (idx n) l

let fold_read
  #state_t
  (#pre: _)
  (#t: Type)
  ()
: Tot (fold_t state_t t t pre (pre))
= fun x -> ret x

noeq
type prog
  (#state_i: Type)
  (state_t: state_i -> Type)
  (action_t: (ret_t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
: (t: typ) -> (ret_t: Type) -> state_i -> (state_i) -> Type
= | PRet:
      (#ret_t: Type) ->
      (#i: state_i) ->
      (#t: typ) ->
      (v: ret_t) ->
      prog state_t action_t t ret_t i (i)
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
      (g: ((x: ret1) -> prog state_t action_t t ret2 (post1) post2)) ->
      prog state_t action_t t ret2 pre1 post2
  | PU8:
      // the base action on a leaf type just reads the value;
      // use PBind with PAction and others to perform operations on that value
      (i: state_i) ->
      prog state_t action_t TU8 U8.t i (i)
  | PPair:
      (#t1: _) ->
      (#t2: _) ->
      (#ret1: _) ->
      (#pre1: _) ->
      (#post1: _) ->
      (f1: prog state_t action_t t1 ret1 pre1 post1) ->
      (#ret2: _) ->
      (#post2: _) ->
      (f2: ((x: ret1) -> prog state_t action_t t2 ret2 (post1) post2)) ->
      prog state_t action_t (TPair t1 t2) ret2 pre1 post2
  | PList:
      (#t: typ) ->
      (inv: _) ->
      prog state_t action_t t unit inv (inv) ->
      prog state_t action_t (TList t) unit inv (inv)
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
  | PRet v -> action_fold (ret v) <: fold_t state_t (type_of_typ t) ret_t _ (_)
  | PAction a -> action_fold (action_sem a)
  | PBind s p -> bind_fold (sem action_sem s) (fun x -> sem action_sem (p x))
  | PU8 _ -> fold_read () <: fold_t state_t (type_of_typ t) ret_t _ (_)
  | PPair p1 p2 -> fold_pair (sem action_sem p1) (fun r -> sem action_sem (p2 r))
  | PList inv p -> fold_list inv (sem action_sem p)
  | PChoice p -> fold_choice (fun x -> sem action_sem (p x)) <: fold_t state_t (type_of_typ (TChoice _)) ret_t pre post

let pseq
  #state_t #action_t
  (#t: typ)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#post2: _)
  (f: prog state_t action_t t unit pre1 post1)
  (g: prog state_t action_t t ret2 (post1) post2)
: Tot (prog state_t action_t t ret2 pre1 post2)
= PBind f (fun _ -> g)

(* Step-by-step serialization *)

noeq
type base_context_t
  (erase_values: bool)
  : typ -> typ -> Type
= | CPairR: (l: typ) -> (r: typ) -> base_context_t erase_values r (TPair l r)
  | CPairL: (l: typ) -> (r: typ) -> (vr: (if erase_values then unit else type_of_typ r)) -> base_context_t erase_values l (TPair l r)
  | CListCons: (t: typ) -> (l: (if erase_values then unit else list (type_of_typ t))) -> base_context_t erase_values t (TList t)
  | CChoicePayload: (f: (bool -> typ)) -> (t': typ) -> base_context_t erase_values t' (TChoice f) // tag is not serialized yet

let base_context_erase_values
  (#erase_values: bool)
  (#t1: _)
  (#t2: _)
  (x: base_context_t erase_values t1 t2)
: Tot (base_context_t true t1 t2)
= match x with
  | CPairL l r _ -> CPairL l r ()
  | CPairR l r -> CPairR l r
  | CListCons t _ -> CListCons t ()
  | CChoicePayload f t' -> CChoicePayload f t'

noeq
type context_t
  (erase_values: bool)
  : typ -> typ -> Type
= | CNil: (#t: typ) -> context_t erase_values t t
  | CCons: (#t1: typ) -> (#t2: typ) -> (#t3: typ) -> (bc: base_context_t erase_values t1 t2) -> (c: context_t erase_values t2 t3) -> context_t erase_values t1 t3

let rec context_erase_values
  (#erase_values: bool)
  (#t1 #t2: _)
  (x: context_t erase_values t1 t2)
: Tot (context_t true t1 t2)
  (decreases x)
= match x with
  | CNil -> CNil
  | CCons b c -> CCons (base_context_erase_values b) (context_erase_values c)


let rec concat_contexts
  (#erase_values: _)
  (#t1 #t2 #t3: _)
  (c12: context_t erase_values t1 t2)
  (c23: context_t erase_values t2 t3)
: Tot (context_t erase_values t1 t3)
  (decreases c12)
= match c12 with
  | CNil -> c23
  | CCons b15 c52 -> CCons b15 (concat_contexts c52 c23)

let rec erase_values_concat_contexts
  (#erase_values: _)
  (#t1 #t2 #t3: _)
  (c12: context_t erase_values t1 t2)
  (c23: context_t erase_values t2 t3)
: Lemma
  (ensures (context_erase_values (concat_contexts c12 c23) == concat_contexts (context_erase_values c12) (context_erase_values c23)))
  (decreases c12)
= match c12 with
  | CNil -> ()
  | CCons b15 c52 -> erase_values_concat_contexts c52 c23

noeq
type hole_or_value_t
  (erase_values: bool)
: typ -> Type
= | HVHole: (t: typ) -> hole_or_value_t erase_values t
  | HVIncompleteList: (t: typ) -> (v: (if erase_values then unit else list (type_of_typ t))) -> hole_or_value_t erase_values (TList t)
  | HVChoicePayload: (f: (bool -> typ)) -> (t': typ) -> (v: (if erase_values then unit else type_of_typ t')) -> hole_or_value_t erase_values (TChoice f)
  | HVValue: (t: typ) -> (v: (if erase_values then unit else type_of_typ t)) -> hole_or_value_t erase_values t

let hole_or_value_erase_values
  (#erase_values: _)
  (#t: _)
  (h: hole_or_value_t erase_values t)
: Tot (hole_or_value_t true t)
= match h with
  | HVHole t -> HVHole t
  | HVIncompleteList t _ -> HVIncompleteList t ()
  | HVChoicePayload f t' _ -> HVChoicePayload f t' ()
  | HVValue t _ -> HVValue t ()

noeq
type hole_t
  (erase_values: bool)
= {
  leaf: typ;
  root: typ;
  context: context_t erase_values leaf root;
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

let hole_concat_context
  (#erase_values: bool)
  (#t: typ)
  (x: hole_t erase_values)
  (c: context_t erase_values x.root t)
: Tot (hole_t erase_values)
= {
    root = t;
    leaf = x.leaf;
    context = concat_contexts x.context c;
    hole = x.hole;
  }

let erase_values_hole_concat_context
  (#erase_values: bool)
  (#t: typ)
  (x: hole_t erase_values)
  (c: context_t erase_values x.root t)
: Lemma
  (hole_erase_values (hole_concat_context x c) == hole_concat_context (hole_erase_values x) (context_erase_values c))
= erase_values_concat_contexts x.context c

let close_hole
  (#erase_values: bool)
  (x: hole_t erase_values {
    CCons? x.context /\
    HVValue? x.hole
  })
: Tot (hole_t erase_values)
= let CCons c c' = x.context in
  let HVValue _ v = x.hole in
  match c with
  | CPairR l r ->
    {
      root = x.root;
      leaf = l;
      context = CCons (CPairL l r v) c';
      hole = HVHole _;
    }
  | CPairL l r vr ->
    {
      root = x.root;
      leaf = _;
      context = c';
      hole = HVValue _ (if erase_values then () else (v, vr));
    }
  | CListCons t l ->
    {
      root = x.root;
      leaf = _;
      context = c';
      hole = HVIncompleteList t (if erase_values then () else v::l);
    }
  | CChoicePayload f _ ->
    {
      root = x.root;
      leaf = _;
      context = c';
      hole = HVChoicePayload f _ (if erase_values then () else v)
    }

let fill_hole
  (#erase_values: bool)
  (x: hole_t erase_values {
    HVHole? x.hole
  })
  (v: (if erase_values then unit else type_of_typ x.leaf))
: Tot (hole_t erase_values)
= {
    x with
    hole = HVValue _ v;
  }

let start_pair
  (#erase_values: bool)
  (x: hole_t erase_values {
    HVHole? x.hole /\
    TPair? x.leaf
  })
: Tot (hole_t erase_values)
= let TPair l r = x.leaf in
  {
    root = x.root;
    leaf = r;
    context = CCons (CPairR l r) x.context;
    hole = HVHole _;
  }

let start_list
  (#erase_values: bool)
  (x: hole_t erase_values {
    HVHole? x.hole /\
    TList? x.leaf
  })
: Tot (hole_t erase_values)
= let TList t = x.leaf in
  {
    x with
    hole = HVIncompleteList t (if erase_values then () else ([] <: list (type_of_typ t)));
  }

let list_cons
  (#erase_values: bool)
  (x: hole_t erase_values {
    HVIncompleteList? x.hole /\
    TList? x.leaf
  })
: Tot (hole_t erase_values)
= let TList t = x.leaf in
  let HVIncompleteList _ l = x.hole in
  {
    root = x.root;
    leaf = t;
    context = CCons (CListCons t l) x.context;
    hole = HVHole _;
  }

let end_list
  (#erase_values: bool)
  (x: hole_t erase_values {
    HVIncompleteList? x.hole
  })
: Tot (hole_t erase_values)
= let TList t = x.leaf in
  {
    x with
    hole = HVValue (TList t) (if erase_values then () else ([] <: list (type_of_typ t)));
  }

let start_choice
  (#erase_values: bool)
  (x: hole_t erase_values {
    HVHole? x.hole /\
    TChoice? x.leaf
  })
  (t': typ)
: Tot (hole_t erase_values)
= let TChoice f = x.leaf in
  {
    root = x.root;
    leaf = t';
    context = CCons (CChoicePayload f t') x.context;
    hole = HVHole _;
  }

let mk_choice_value
  (tag: bool)
  (f: bool -> typ)
  (v: type_of_typ (f tag))
: Tot (type_of_typ (TChoice f))
= (| tag, v |)

let end_choice
  (#erase_values: bool)
  (x: hole_t erase_values)
  (tag: bool {
    HVChoicePayload? x.hole /\
    begin let HVChoicePayload f t' _ = x.hole in
    f tag == t'
    end
  })
: Tot (hole_t erase_values)
= let HVChoicePayload f t' v = x.hole in
  {
    x with
    hole = HVValue _ (if erase_values then () else mk_choice_value tag f v);
  }

let ser_index (root: typ) : Type0 = (h: hole_t true { h.root == root })

let ser_state (#root: typ) (i: ser_index root) : Tot Type0 = (x: hole_t false {
  hole_erase_values x == i
})

let ser_close_hole
  (#root: typ)
  (x: ser_index root)
  (sq: squash (
    CCons? x.context /\
    HVValue? x.hole
  ))
: Tot (stt ser_state unit x (close_hole x))
= fun h -> ((), close_hole h)

let ser_u8
  (#root: typ)
  (x: ser_index root)
  (v: U8.t {
    x.leaf == TU8 /\
    HVHole? x.hole
  })
: Tot (stt ser_state unit x (fill_hole x ()))
= fun h -> ((), fill_hole h v)

let ser_start_pair
  (#root: typ)
  (x: ser_index root)
  (sq: squash (
    TPair? x.leaf /\
    HVHole? x.hole
  ))
: Tot (stt ser_state unit x (start_pair x))
= fun h -> ((), start_pair h)

noeq
type ser_action
  (#root: typ)
: (ret_t: Type) -> ser_index root -> (ser_index) root -> Type
= | SCloseHole:
      (#x: ser_index root) ->
      squash (CCons? x.context /\ HVValue? x.hole) ->
      ser_action unit x (close_hole x)
  | SU8:
      (#x: ser_index root) ->
      (v: U8.t) ->
      squash (
        x.leaf == TU8 /\
        HVHole? x.hole
      ) ->
      ser_action unit x (fill_hole x ())
  | SStartPair:
      (#x: ser_index root) ->
      squash (TPair? x.leaf /\ HVHole? x.hole) ->
      ser_action unit x (start_pair x)

let ser_action_sem
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (a: ser_action ret_t pre post)
: Tot (stt ser_state ret_t pre post)
= match a with
  | SCloseHole #_ #x _ -> ser_close_hole x ()
  | SU8 #_ #x v _ -> ser_u8 x v
  | SStartPair #_ #x _ -> ser_start_pair x ()

let ser_action_concat_context
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (#t': typ)
  (a: ser_action ret_t pre post)
  (c: context_t true pre.root t')
: Tot (ser_action ret_t (hole_concat_context pre c) (hole_concat_context post c))
= match a with
  | SCloseHole _ -> SCloseHole ()
  | SU8 v _ -> SU8 v ()
  | SStartPair _ -> SStartPair #t' ()

#push-options "--z3rlimit 16"
#restart-solver

let sem_ser_action_concat_context
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (#t': typ)
  (a: ser_action ret_t pre post)
  (s: ser_state pre)
  (c: context_t false pre.root t')
: Lemma
  (
    let (v, s') = ser_action_sem a s in
    let sc = hole_concat_context s c in
    hole_erase_values sc == hole_concat_context pre (context_erase_values c) /\
    ser_action_sem (ser_action_concat_context a (context_erase_values c)) sc ==
      (v, hole_concat_context s' c)
  )
=
  let (v, s') = ser_action_sem a s in
  let sc = hole_concat_context s c in
  erase_values_hole_concat_context s c

#pop-options

let rec prog_concat_context
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (#ty: typ)
  (#t': typ)
  (p: prog ser_state ser_action ty ret_t pre post)
  (c: context_t true pre.root t')
: Tot (prog ser_state (ser_action #t') ty ret_t (hole_concat_context pre c) (hole_concat_context post c))
  (decreases p)
= match p with
  | PRet v -> PRet v
  | PAction a -> PAction (ser_action_concat_context a c)
  | PBind f g -> PBind (prog_concat_context f c) (fun x -> prog_concat_context (g x) c)
  | PU8 i -> PU8 (hole_concat_context i c)
  | PPair f1 f2 -> PPair (prog_concat_context f1 c) (fun x -> prog_concat_context (f2 x) c)
  | PList i f -> PList _ (prog_concat_context f c)
  | PChoice f -> PChoice (fun x -> prog_concat_context (f x) c)

let rec fold_list_concat_context
  (#root: typ)
  (#inv: ser_index root)
  (#t: Type)
  (f: fold_t ser_state t unit inv inv)
  (#t': typ)
  (c: context_t false root t')
  (g: fold_t (ser_state #t') t unit (hole_concat_context inv (context_erase_values c)) (hole_concat_context inv (context_erase_values c)))
  (prf: (i: t) -> (s: ser_state inv) ->
    Lemma
    (requires (
      let (v, s') = f i s in
      hole_erase_values (hole_concat_context s c) == hole_concat_context (hole_erase_values s) (context_erase_values c) /\
      hole_erase_values (hole_concat_context s' c) == hole_concat_context (hole_erase_values s') (context_erase_values c)
    ))
    (ensures (let (v, s') = f i s in
      g i (hole_concat_context s c) == (v, hole_concat_context s' c)
    ))
  )
  (input: list t)
  (s: ser_state inv)
: Lemma
  (ensures (
    let (v, s') = fold_list inv f input s in
    hole_erase_values (hole_concat_context s c) == hole_concat_context (hole_erase_values s) (context_erase_values c) /\
    hole_erase_values (hole_concat_context s' c) == hole_concat_context (hole_erase_values s') (context_erase_values c) /\
    fold_list (hole_concat_context inv (context_erase_values c)) g input (hole_concat_context s c) ==
      (v, hole_concat_context s' c)
  ))
  (decreases input)
= erase_values_hole_concat_context s c;
  match input with
  | [] -> ()
  | hd :: tl ->
    let (_, s') = f hd s in
    erase_values_hole_concat_context s' c;
    prf hd s;
    fold_list_concat_context f c g prf tl s'

#push-options "--split_queries" // "--z3rlimit 64"
#restart-solver

let rec sem_prog_concat_context
  (#root: typ)
  (#ret_t: Type)
  (#pre: ser_index root)
  (#post: (ser_index root))
  (#ty: typ)
  (#t': typ)
  (p: prog ser_state ser_action ty ret_t pre post)
  (input: type_of_typ ty)
  (s: ser_state pre)
  (c: context_t false root t')
: Lemma
  (ensures (
    let (v, s') = sem ser_action_sem p input s in
    let sc = hole_concat_context s c in
    let sc' = hole_concat_context s' c in
    hole_erase_values sc == hole_concat_context pre (context_erase_values c) /\
    hole_erase_values sc' == hole_concat_context post (context_erase_values c) /\
    sem ser_action_sem (prog_concat_context p (context_erase_values c)) input sc ==
      (v, sc')
  ))
  (decreases p)
= 
  let (v, s') = sem ser_action_sem p input s in
  let sc = hole_concat_context s c in
  let sc' = hole_concat_context s' c in
  erase_values_hole_concat_context s c;
  erase_values_hole_concat_context s' c;
  match p with
  | PAction a ->
    sem_ser_action_concat_context a s c
  | PBind f g ->
    sem_prog_concat_context f input s c;
    let (vf, sf) = sem ser_action_sem f input s in
    sem_prog_concat_context (g vf) input sf c
  | PPair #_ #_ #_ #t1 #t2 f1 f2 ->
    let (i1, i2) = (input <: (type_of_typ t1 & type_of_typ t2)) in
    sem_prog_concat_context f1 i1 s c;
    let (v1, s1) = sem ser_action_sem f1 i1 s in
    sem_prog_concat_context (f2 v1) i2 s1 c
  | PU8 _ -> ()
  | PRet _ -> ()
  | PChoice #_ #_ #_ #t f ->
    let (| tag, pl |) = (input <: (type_of_typ (TChoice t))) in
    sem_prog_concat_context (f tag) pl s c
  | PList inv body ->
    fold_list_concat_context
      (sem ser_action_sem body)
      c
      (sem ser_action_sem (prog_concat_context body (context_erase_values c)))
      (fun elt st ->
        sem_prog_concat_context body elt st c
      )
      input
      s

#pop-options

let initial_ser_index
  (ty: typ)
: Tot (ser_index ty)
= Mkhole_t ty _ CNil (HVHole _)

let final_ser_index
  (ty: typ)
: Tot (ser_index ty)
= Mkhole_t ty _ CNil (HVValue _ ())

let initial_ser_state
  (ty: typ)
: Tot (ser_state (initial_ser_index ty))
= {
    root = ty;
    leaf = _;
    context = CNil;
    hole = HVHole _;
  }

let initial_ser_state_complete
  (ty: typ)
: Lemma
  (forall (s: ser_state (initial_ser_index ty)) . s == initial_ser_state ty)
= ()

let final_ser_state
  (ty: typ)
  (v: type_of_typ ty)
: Tot (ser_state (final_ser_index ty))
= {
    root = ty; leaf = _; context = CNil; hole = HVValue _ v;
  }

let test1 : prog ser_state ser_action _ _ (initial_ser_index (TPair TU8 TU8)) _ =
  PBind
    (PAction (SStartPair ()))
    (fun _ ->
       PPair
         (PBind
            (PU8 _)
            (fun v ->
              PBind
                (PAction (SU8 v ()))
                (fun _ -> PAction (SCloseHole ()))
            )
         )
         (fun _ ->
          PBind
            (PU8 _)
            (fun v ->
              PBind
                (PAction (SU8 v ()))
                (fun _ -> PAction (SCloseHole ()))
            )
         )
    )

let _ : squash (forall (v: type_of_typ (TPair TU8 TU8)) s . sem ser_action_sem test1 v s == ((), final_ser_state (TPair TU8 TU8) (snd v, fst v))) =
  assert_norm (forall (v: type_of_typ (TPair TU8 TU8)) . sem ser_action_sem test1 v (initial_ser_state (TPair TU8 TU8)) == ((), final_ser_state (TPair TU8 TU8) (snd v, fst v)))

let test2 : prog ser_state ser_action _ _ (initial_ser_index (TPair TU8 TU8)) _ (* final_ser_index (TPair TU8 TU8) *) =
  PPair
    (PU8 _)
    (fun lhs -> PBind
      (PU8 _)
      (fun rhs -> PBind
        (PAction (SStartPair ()))
        (fun _ -> PBind
          (PAction (SU8 lhs ()))
          (fun _ -> PBind
            (PAction (SCloseHole ()))
            (fun _ -> PBind
              (PAction (SU8 rhs ()))
              (fun _ -> PAction (SCloseHole ()))
            )
          )
        )
      )
    )

let _ : squash (forall (v: type_of_typ (TPair TU8 TU8)) s . sem ser_action_sem test2 v s == ((), final_ser_state (TPair TU8 TU8) (snd v, fst v))) =
  assert_norm (forall (v: type_of_typ (TPair TU8 TU8)) . sem ser_action_sem test2 v (initial_ser_state (TPair TU8 TU8)) == ((), final_ser_state (TPair TU8 TU8) (snd v, fst v)))

(*
frame_out :
  (ty: typ) ->
  prog ser_state ser_action _ _ (initial_ser_index ty) (final_ser_index ty) ->
  (c: ctxt) ->
  prog ser_state ser_action _ _ (c `prepend` initial_ser_index ty) (c `prepend` final_ser_index ty)

PBind
  PBind (SStartPair ()) PBind (frame_out test2) (SCloseHole ())
  PBind (SStartPair ()) PBind (frame_out test2) (SCloseHole ())
*)

let test3 : prog ser_state ser_action _ _ (initial_ser_index (TPair TU8 TU8)) _ =
  PPair
    (PU8 _)
    (fun lhs -> PBind
      (PU8 _)
      (fun rhs -> PBind
        (PAction (SStartPair ()))
        (fun _ -> PBind
          (PAction (SU8 rhs ()))
          (fun _ -> PBind
            (PAction (SCloseHole ()))
            (fun _ -> PBind
              (PAction (SU8 lhs ()))
              (fun _ -> PAction (SCloseHole ()))
            )
          )
        )
      )
    )

let _ : squash (forall (v: type_of_typ (TPair TU8 TU8)) s . sem ser_action_sem test3 v s == ((), final_ser_state (TPair TU8 TU8) v)) =
  assert_norm (forall (v: type_of_typ (TPair TU8 TU8)) . sem ser_action_sem test3 v (initial_ser_state (TPair TU8 TU8)) == ((), final_ser_state (TPair TU8 TU8) v))
