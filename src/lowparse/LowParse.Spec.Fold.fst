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
type hole_t
  : typ -> Type
= | HU8: hole_t TU8
  | HPairL: (l: typ) -> hole_t l -> (r: typ) -> hole_t (TPair l r)
  | HPairR: (l: typ) -> (v: type_of_typ l) -> (r: typ) -> hole_t r -> hole_t (TPair l r)
  | HList: (t: typ) -> (l: list (type_of_typ t)) -> hole_t (TList t)
  | HListCons: (t: typ) -> (l: list (type_of_typ t)) -> hole_t t -> hole_t (TList t)
  | HChoiceTag: (f: (bool -> typ)) -> hole_t (TChoice f)
  | HChoicePayload: (f: (bool -> typ)) -> (tag: bool) -> hole_t (f tag) -> hole_t (TChoice f)

let rec init_hole
  (t: typ)
: Tot (hole_t t)
= match t with
  | TU8 -> HU8
  | TPair l r -> HPairL l (init_hole l) r
  | TList t -> HList t []
  | TChoice f -> HChoiceTag f

noeq
type hole_or_value_t
  (t: typ)
= | Value: type_of_typ t -> hole_or_value_t t
  | Hole: hole_t t -> hole_or_value_t t

noeq
type transition
  : (#t: typ) -> hole_t t -> hole_or_value_t t -> Type
= | TransU8: (v: U8.t) -> transition HU8 (Value v)
  | TransPairLH: (l: typ) -> (h1: hole_t l) -> (h2: hole_t l) -> transition h1 (Hole h2) -> (r: typ) -> transition (HPairL l h1 r) (Hole (HPairL l h2 r))
  | TransPairLV: (l: typ) -> (h: hole_t l) -> (v: type_of_typ l) -> transition h (Value v) -> (r: typ) -> transition (HPairL l h r) (Hole (HPairR l v r (init_hole r)))
  | TransPairRH: (l: typ) -> (v: type_of_typ l) -> (r: typ) -> (h1: hole_t r) -> (h2: hole_t r) -> transition h1 (Hole h2) -> transition (HPairR l v r h1) (Hole (HPairR l v r h2))
  | TransPairRV: (l: typ) -> (vl: type_of_typ l) -> (r: typ) -> (h: hole_t r) -> (vr: type_of_typ r) -> transition h (Value vr) -> transition (HPairR l vl r h) (Value (vl, vr))
  | TransListNil: (t: typ) -> (l: list (type_of_typ t)) -> transition (HList t l) (Value l)
  | TransListSnoc: (t: typ) -> (l: list (type_of_typ t)) -> transition (HList t l) (Hole (HListCons t l (init_hole t)))
  | TransListSnocH: (t: typ) -> (l: list (type_of_typ t)) -> (h1: hole_t t) -> (h2: hole_t t) -> transition (HListCons t l h1) (Hole (HListCons t l h2))
  | TransListSnocV: (t: typ) -> (l: list (type_of_typ t)) -> (h: hole_t t) -> (v: type_of_typ t) -> transition h (Value v) -> transition (HListCons t l h) (Hole (HList t (l `List.Tot.append` [v])))
  | TransListChoiceTag: (f: (bool -> typ)) -> (tag: bool) -> transition (HChoiceTag f) (Hole (HChoicePayload f tag (init_hole (f tag))))
  | TransListChoicePayloadH: (f: (bool -> typ)) -> (tag: bool) -> (h1: hole_t (f tag)) -> (h2: hole_t (f tag)) -> transition h1 (Hole h2) -> transition (HChoicePayload f tag h1) (Hole (HChoicePayload f tag h2))
  | TransListChoicePayloadV: (f: (bool -> typ)) -> (tag: bool) -> (h: hole_t (f tag)) -> (v: type_of_typ (f tag)) -> transition h (Value v) -> transition (HChoicePayload f tag h) (Value (| tag, v |))
