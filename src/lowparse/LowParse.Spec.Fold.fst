module LowParse.Spec.Fold
include LowParse.Spec.Combinators

module U8 = FStar.UInt8
module SZ = FStar.SizeT

// to be used with delta_attr to compute the Steel code synthesis
// before extraction to C
noeq type specialize : Type0 =

[@@specialize]
noeq
type typ
  (#scalar_t: Type u#a)
  (type_of_scalar: (scalar_t -> Type u#(max a b)))
: (* nonempty: *) bool -> (* must_be_size_prefixed: *) bool -> Type u#(max a b)
=
| TFalse: (ne: bool) -> (pr: bool) -> typ type_of_scalar ne pr
| TUnit: typ type_of_scalar false false
| TScalar: scalar_t -> typ type_of_scalar true false
| TPair: (#ne1: bool) -> typ type_of_scalar ne1 false ->  (#ne2: bool) -> (#pr2: bool) -> typ type_of_scalar ne2 pr2 -> typ type_of_scalar (ne1 || ne2) pr2
| TIf:
    (#ne: bool) ->
    (#pr: bool) ->
    (b: bool) -> 
    (squash (b == true) -> typ type_of_scalar ne pr) ->
    (squash (b == false) -> typ type_of_scalar ne pr) ->
    typ type_of_scalar ne pr
| TChoice: (s: scalar_t) -> (#ne: bool) -> (#pr: bool) -> (type_of_scalar s -> typ type_of_scalar ne pr) -> typ type_of_scalar true pr
| TSizePrefixed: (s: scalar_t) -> (sz: (type_of_scalar s -> SZ.t) {synth_injective sz}) -> (#ne: bool) -> (#pr: bool) -> typ type_of_scalar ne pr -> typ type_of_scalar true false
| TList: typ type_of_scalar true false -> typ type_of_scalar false true

let type_of_payload
  (#scalar_t: Type)
  (type_of_scalar: (scalar_t -> Type))
  (s: scalar_t)
  (#ne #pr: bool)
  (f: type_of_scalar s -> typ type_of_scalar ne pr { forall (x: type_of_scalar s) . f x << TChoice s f })
  (type_of_typ: ((t: typ type_of_scalar ne pr { t << TChoice s f }) -> Tot Type0))
  (x: type_of_scalar s)
: Tot Type0
= type_of_typ (f x)

[@@specialize] // mostly for scalar types
let rec type_of_typ
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (#ne #pr: bool)
  (t: typ type_of_scalar ne pr)
: Tot Type
  (decreases t)
= match t with
| TScalar s -> type_of_scalar s
| TPair t1 t2 -> (type_of_typ t1 & type_of_typ t2)
| TList t' -> list (type_of_typ t') // we ignore the serializer for now
| TIf b ttrue tfalse -> if b then type_of_typ (ttrue ()) else type_of_typ (tfalse ())
| TChoice s f -> dtuple2 (type_of_scalar s) (type_of_payload type_of_scalar s f type_of_typ)
| TSizePrefixed _ _ t -> type_of_typ t
| TUnit -> unit
| TFalse _ _ -> squash False

let type_of_payload'
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: scalar_t)
  (#ne #pr: bool)
  (f: type_of_scalar s -> typ type_of_scalar ne pr)
: Pure (type_of_scalar s -> Type)
    (requires True)
    (ensures (fun v ->
      type_of_typ (TChoice s f) == dtuple2 (type_of_scalar s) v /\
      (forall x . v x == type_of_typ (f x))
    ))
= let v = fun x -> type_of_typ (f x) in
  assert_norm (type_of_typ (TChoice s f) == dtuple2 (type_of_scalar s) v);
  v

let mk_choice_value
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (s: scalar_t)
  (tag: type_of_scalar s)
  (#ne #pr: bool)
  (f: (type_of_scalar s -> typ type_of_scalar ne pr))
  (v: type_of_typ (f tag))
: Tot (type_of_typ (TChoice s f))
= let v' : dtuple2 (type_of_scalar s) (type_of_payload' s f) = (| tag, v |) in
  v'

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
  (#tk: Type)
  (#t: tk -> Type)
  (#pre: state_i)
  (#post: _)
  (f: (x: tk) -> fold_t state_t (t x) ret_t pre post)
: Tot (fold_t state_t (dtuple2 tk t) ret_t pre post)
= fun w -> f (dfst w) (dsnd w)

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
  (from: nat) (to: nat)
  (f: (x: nat { from <= x /\ x < to }) -> fold_t state_t t unit inv inv)
: Tot (fold_t state_t t unit inv inv)
  (decreases (if to <= from then 0 else to - from + 1))
= if from >= to
  then action_fold (ret ())
  else bind_fold (f from) (fun _ -> fold_for inv (from + 1) to f)

let nlist (n: nat) (t: Type) = (l: list t { List.Tot.length l == n })

let fold_list_index
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (n: nat)
  (idx: (i: nat { i < n }))
  (f: fold_t state_t t unit inv inv)
: Tot (fold_t state_t (nlist n t) unit inv inv)
= fun l -> f (List.Tot.index l idx)

let fold_list_index_of
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (n: nat)
  (idx: (i: nat { i < n }) -> Tot (i: nat { i < n }))
  (j: nat {j < n})
: Tot (fold_t state_t (nlist n t) unit inv inv)
= fold_list_index inv n (idx j) f

let fold_for_list'
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (n: nat)
  (idx: (i: nat { i < n }) -> Tot (i: nat { i < n }))
: Tot (fold_t state_t (nlist n t) unit inv inv)
= fold_for inv 0 n (fold_list_index_of inv f n idx)

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

module SZ = FStar.SizeT

inline_for_extraction
noeq
type array_index_fn = {
  array_index_f_nat: ((n: nat) -> (x: nat {x < n}) -> (y: nat {y < n}));
  array_index_f_sz: ((n: SZ.t) -> (x: SZ.t) -> Pure SZ.t (SZ.v x < SZ.v n) (fun y -> SZ.v y == array_index_f_nat (SZ.v n) (SZ.v x)));
}

inline_for_extraction
let array_index_reverse = {
  array_index_f_nat = (fun n x -> n - 1 - x);
  array_index_f_sz = (fun n x -> (n `SZ.sub` 1sz) `SZ.sub` x);
}

noeq
type prog
  (#scalar_t: Type0)
  (type_of_scalar: (scalar_t -> Type0))
  (#state_i: Type u#a)
  (state_t: state_i -> Type u#b)
  (action_t: (ret_t: Type0) -> (pre: state_i) -> (post: state_i) -> Type u#c)
: (#ne: bool) -> (#pr: bool) -> (t: typ type_of_scalar ne pr) -> (ret_t: Type0) -> state_i -> (state_i) -> Type u#(max 1 a b c)
=
  | PRet:
      (#ret_t: Type) ->
      (#i: state_i) ->
      (#ne: bool) ->
      (#pr: bool) ->
      (#t: typ type_of_scalar ne pr) ->
      (v: ret_t) ->
      prog type_of_scalar state_t action_t t ret_t i (i)
  | PAction:
      (#ne: bool) ->
      (#pr: bool) ->
      (#t: typ type_of_scalar ne pr) ->
      (#ret_t: Type) -> (#pre: _) -> (#post: _) ->
      action_t ret_t pre post ->
      prog type_of_scalar state_t action_t t ret_t pre post
  | PBind:
      (#ne: bool) ->
      (#pr: bool) ->
      (#t: typ type_of_scalar ne pr) ->
      (#ret1: Type) ->
      (#pre1: _) ->
      (#post1: _) ->
      (#ret2: _) ->
      (#post2: _) ->
      (f: prog type_of_scalar state_t action_t t ret1 pre1 post1) ->
      (g: ((x: ret1) -> prog type_of_scalar state_t action_t t ret2 (post1) post2)) ->
      prog type_of_scalar state_t action_t t ret2 pre1 post2
  | PIfP:
      (#ne: bool) ->
      (#pr: bool) ->
      (#t: typ type_of_scalar ne pr) ->
      (#ret: Type) ->
      (#pre: state_i) ->
      (#post: state_i) ->
      (x: bool) ->
      (squash (x == true) -> prog type_of_scalar state_t action_t t ret pre post) ->
      (squash (x == false) -> prog type_of_scalar state_t action_t t ret pre post) ->
      prog type_of_scalar state_t action_t t ret pre post
  | PIfT:
      (#ret_t: Type) ->
      (#pre: state_i) ->
      (#post: state_i) ->
      (b: bool) ->
      (#ne: bool) ->
      (#pr: bool) ->
      (#ttrue: (squash (b == true) -> typ type_of_scalar ne pr)) ->
      (ptrue: (squash (b == true) -> prog type_of_scalar state_t action_t (ttrue ()) ret_t pre post)) ->
      (#tfalse: (squash (b == false) -> typ type_of_scalar ne pr)) ->
      (pfalse: (squash (b == false) -> prog type_of_scalar state_t action_t (tfalse ()) ret_t pre post)) ->
      prog type_of_scalar state_t action_t (TIf b ttrue tfalse) ret_t pre post
  | PScalar:
      // the base action on a leaf type just reads the value;
      // use PBind with PAction and others to perform operations on that value
      (i: state_i) ->
      (s: scalar_t) ->
      prog type_of_scalar state_t action_t (TScalar s) (type_of_scalar s) i (i)
  | PPair:
      (#ne1: bool) ->
      (#t1: typ type_of_scalar ne1 false) ->
      (#ne2: bool) ->
      (#pr2: bool) ->
      (#t2: typ type_of_scalar ne2 pr2) ->
      (#ret1: _) ->
      (#pre1: _) ->
      (#post1: _) ->
      (f1: prog type_of_scalar state_t action_t t1 ret1 pre1 post1) ->
      (#ret2: _) ->
      (#post2: _) ->
      (f2: ((x: ret1) -> prog type_of_scalar state_t action_t t2 ret2 (post1) post2)) ->
      prog type_of_scalar state_t action_t (TPair t1 t2) ret2 pre1 post2
  | PList:
      (#t: typ type_of_scalar true false) ->
      (inv: _) ->
      prog type_of_scalar state_t action_t t unit inv (inv) ->
      prog type_of_scalar state_t action_t (TList t) unit inv (inv)
  | PListFor:
      (#t: typ type_of_scalar true false) ->
      (inv: _) ->
      (idx: array_index_fn) ->
      prog type_of_scalar state_t action_t t unit inv (inv) ->
      prog type_of_scalar state_t action_t (TList t) unit inv (inv)
  | PChoice:
      (#s: scalar_t) ->
      (#ne: bool) ->
      (#pr: bool) ->
      (#t: (type_of_scalar s -> typ type_of_scalar ne pr)) ->
      (#ret_t: Type) ->
      (#pre: _) ->
      (#post: _) ->
      ((x: type_of_scalar s) -> prog type_of_scalar state_t action_t (t x) ret_t pre post) ->
      prog type_of_scalar state_t action_t (TChoice s t) ret_t pre post
  | PSizePrefixed:
      (#ret_t: Type) ->
      (#ne: bool) ->
      (#pr: bool) ->
      (#t: typ type_of_scalar ne pr) ->
      (s: scalar_t) ->
      (sz: (type_of_scalar s -> SZ.t) {synth_injective sz}) ->
      (#pre: _) ->
      (#post: _) ->
      prog type_of_scalar state_t action_t t ret_t pre post ->
      prog type_of_scalar state_t action_t (TSizePrefixed s sz t) ret_t pre post

[@@specialize]
let pbind
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (#state_i: Type u#a)
  (#state_t: state_i -> Type u#b)
  (#action_t: (ret_t: Type) -> (pre: state_i) -> (post: state_i) -> Type u#c)
  (#ne #pr: bool)
  (#t: typ type_of_scalar ne pr)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#post2: _)
  (f: prog type_of_scalar state_t action_t t ret1 pre1 post1)
  (g: ((pre2: state_i) -> squash (pre2 == post1) -> (x: ret1) -> prog type_of_scalar state_t action_t t ret2 pre2 post2))
: prog type_of_scalar state_t action_t t ret2 pre1 post2
= PBind f (g post1 ())

[@@specialize; noextract_to "krml"]
let typ_of_prog
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  (#state_i: Type)
  (#state_t: state_i -> Type)
  (#action_t: (ret_t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (#ne #pr: bool)
  (#t: typ type_of_scalar ne pr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: prog type_of_scalar state_t action_t t ret_t pre post)
: Tot (typ type_of_scalar ne pr)
= t

let rec sem
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  #state_t
  (#action_t: (t: Type) -> (pre: _) -> (post: _) -> Type)
  (action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
  (#ne #pr: bool)
  (#t: typ type_of_scalar ne pr)
  (#ret_t: Type)
  (#pre: _)
  (#post: _)
  (p: prog type_of_scalar state_t action_t t ret_t pre post)
: Tot (fold_t state_t (type_of_typ t) ret_t pre post)
  (decreases p)
= match p returns (fold_t state_t (type_of_typ t) ret_t pre post) with
  | PRet v -> action_fold (ret v) <: fold_t state_t (type_of_typ t) ret_t _ (_)
  | PAction a -> action_fold (action_sem a)
  | PBind s p -> bind_fold (sem action_sem s) (fun x -> sem action_sem (p x))
  | PIfP x ptrue pfalse -> if x then sem action_sem (ptrue ()) else sem action_sem (pfalse ())
  | PIfT x ptrue pfalse -> if x then coerce _ (sem action_sem (ptrue ())) else coerce _ (sem action_sem (pfalse ()))
  | PScalar _ _ -> fold_read () <: fold_t state_t (type_of_typ t) ret_t _ (_)
  | PPair p1 p2 -> fold_pair (sem action_sem p1) (fun r -> sem action_sem (p2 r))
  | PList inv p -> fold_list inv (sem action_sem p)
  | PListFor inv idx p -> fold_for_list inv (sem action_sem p) idx.array_index_f_nat
  | PChoice #_ #_ #_ #_ #_ #s #_ #_ #t p -> fold_choice #_ #_ #_ #_ #(type_of_payload' s t) (fun x -> sem action_sem (p x))
  | PSizePrefixed _ _ p -> coerce _ (sem action_sem p)

let pseq
  (#scalar_t: Type)
  (#type_of_scalar: (scalar_t -> Type))
  #state_t #action_t
  (#ne #pr: bool)
  (#t: typ type_of_scalar ne pr)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#post2: _)
  (f: prog type_of_scalar state_t action_t t unit pre1 post1)
  (g: prog type_of_scalar state_t action_t t ret2 (post1) post2)
: Tot (prog type_of_scalar state_t action_t t ret2 pre1 post2)
= PBind f (fun _ -> g)
