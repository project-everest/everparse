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

module SZ = LowParse.Steel.StdInt

inline_for_extraction
noeq
type array_index_fn = {
  array_index_f_nat: ((n: nat) -> (x: nat {x < n}) -> (y: nat {y < n}));
  array_index_f_sz: ((n: SZ.size_t) -> (x: SZ.size_t) -> Pure SZ.size_t (SZ.size_v x < SZ.size_v n) (fun y -> SZ.size_v y == array_index_f_nat (SZ.size_v n) (SZ.size_v x)));
}

let array_index_reverse = {
  array_index_f_nat = (fun n x -> n - 1 - x);
  array_index_f_sz = (fun n x -> (n `SZ.size_sub` SZ.one_size) `SZ.size_sub` x);
}

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
  | PListFor:
      (#t: typ) ->
      (inv: _) ->
      (idx: array_index_fn) ->
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
  | PListFor inv idx p -> fold_for_list inv (sem action_sem p) idx.array_index_f_nat
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
