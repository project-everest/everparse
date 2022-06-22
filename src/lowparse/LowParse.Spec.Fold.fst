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

let stt (state_t: Type) (ret_t: Type) : Tot Type = state_t -> (ret_t & state_t)

let ret (#state_t: Type) (#ret_t: Type) (x: ret_t) : Tot (stt state_t ret_t) = fun s -> (x, s)

let bind (#state_t: Type) (#ret1_t #ret2_t: Type) (f1: stt state_t ret1_t) (f2: ret1_t -> stt state_t ret2_t) : Tot (stt state_t ret2_t) =
  fun state ->
    let (r, state) = f1 state in
    f2 r state

let fold_t (state_t: Type) (t: Type) : Tot Type = (t -> stt state_t unit)

let fold_pair
  (#state_t: Type)
  (#t1 #t2: Type)
  (f1: fold_t state_t t1)
  (f2: fold_t state_t t2)
: Tot (fold_t state_t (t1 & t2))
= fun (x1, x2) -> bind (f1 x1) (fun _ -> f2 x2)

let fold_list
  (#state_t: Type)
  (#t: Type)
  (f: fold_t state_t t)
: Tot (fold_t state_t (list t))
= fun l x -> ((), List.Tot.fold_left (fun state x -> snd (f x state)) x l)

let fold_choice
  (#state_t: Type)
  (#t: bool -> Type)
  (f: (x: bool) -> fold_t state_t (t x))
: Tot (fold_t state_t (x: bool & t x))
= fun w -> if (dfst w) then f true (dsnd w) else f false (dsnd w)

let bind_fold
  (#state_t: Type)
  (#ret_t: Type)
  (#t: Type)
  (f: stt state_t ret_t)
  (g: ret_t -> fold_t state_t t)
: Tot (fold_t state_t t)
= fun x -> bind f (fun r -> g r x)

let seq_fold
  (#state_t: Type)
  (#t: Type)
  (f1 f2: fold_t state_t t)
: Tot (fold_t state_t t)
= fun x -> bind (f1 x) (fun _ -> f2 x)

let ret_fold
  (#state_t: Type)
  (#t: Type)
  (f: stt state_t unit)
: Tot (fold_t state_t t)
= fun _ -> f

noeq
type prog
  (state_t: Type)
  (action_t: (t: Type) -> stt state_t t -> Type)
: typ -> Type
= | PRet: (t: typ) -> (s: stt state_t unit) -> action_t _ s -> prog state_t action_t t
  | PSeq: (#t: typ) -> prog state_t action_t t -> prog state_t action_t t -> prog state_t action_t t
  | PBind: (#r: Type) -> (#t: typ) -> (s: stt state_t r) -> action_t r s -> (r -> prog state_t action_t t) -> prog state_t action_t t
  | PU8: (s: (U8.t -> stt state_t unit)) -> ((x: U8.t) -> action_t _ (s x)) -> prog state_t action_t TU8
  | PPair: (#t1: typ) -> (#t2: typ) -> prog state_t action_t t1 -> prog state_t action_t t2 -> prog state_t action_t (TPair t1 t2)
  | PList: (#t: typ) -> prog state_t action_t t -> prog state_t action_t (TList t)
  | PChoice: (f: (bool -> typ)) -> ((x: bool) -> prog state_t action_t (f x)) -> prog state_t action_t (TChoice f)

let rec sem
  (#state_t: Type)
  (#action_t: (t: Type) -> stt state_t t -> Type)
  (#t: typ)
  (p: prog state_t action_t t)
: Tot (fold_t state_t (type_of_typ t))
= match p returns fold_t state_t (type_of_typ t) with
  | PRet _ s _ -> ret_fold s
  | PSeq p1 p2 -> seq_fold (sem p1) (sem p2)
  | PBind s _ p -> bind_fold s (fun x -> sem (p x))
  | PU8 s _ -> s
  | PPair p1 p2 -> fold_pair (sem p1) (sem p2)
  | PList p -> fold_list (sem p)
  | PChoice f p -> fold_choice (fun x -> sem (p x)) <: fold_t state_t (type_of_typ (TChoice f))
